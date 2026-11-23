module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConcretePeriodDatumPadicFiniteExtension
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.PdEx

variable {l : ℕ} [Fact l.Prime]

def actOf {G k B : Type} [Group G] [CommRing k] [CommRing B] [Algebra k B] (s : G → B →+* B)
    (hmul : ∀ g h x, s (g * h) x = s g (s h x)) (hone : ∀ x, s 1 x = x)
    (hk : ∀ g c, s g (algebraMap k B c) = algebraMap k B c) : G →* (B ≃ₐ[k] B) where
  toFun g :=
    { toFun := s g
      invFun := s g⁻¹
      left_inv := fun x => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun x => by rw [← hmul, mul_inv_cancel, hone]
      map_mul' := map_mul (s g)
      map_add' := map_add (s g)
      commutes' := hk g }
  map_one' := AlgEquiv.ext fun x => hone x
  map_mul' g h := AlgEquiv.ext fun x => hmul g h x

def inc (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)

theorem inc_coe (K : FinExt l) (x : ↥(K0 K)) : ((inc K x : ↥(MaximalUnramifiedExtension l)) : Om l) = (x : Om l) := rfl

def sigK (K : FinExt l) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (h : ∀ x : ↥(MaximalUnramifiedExtension l), (x : Om l) ∈ K.1 → ((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(K0 K) :=
  (((MaximalUnramifiedExtension l).val.comp σ).comp (inc K)).codRestrict (K0 K).toSubalgebra fun x =>
    ⟨h (inc K x) x.2.1, (σ (inc K x)).2⟩

theorem inc_sigK (K : FinExt l) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) (h) (x : ↥(K0 K)) :
    inc K (sigK K σ h x) = σ (inc K x) := Subtype.ext rfl

theorem finiteDimensional_maxUnramifiedSubfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) :=
  haveI := K.2
  Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
    (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))

theorem fix (K : FinExt l) (g : ↥(GK K)) (x : Om l) (hx : x ∈ K.1) : (g : GQ l) x = x :=
  (IntermediateField.mem_fixingSubgroup_iff K.1 (g : GQ l)).1 g.2 x hx

theorem exists_abstract (R : LocRings l) (K : FinExt l)
    (sB : GQ l → R.B →+* R.B) (sD : GQ l → R.BdR →+* R.BdR) (φ : R.B →+* R.B) (ι : R.B →+* R.BdR)
    (F : ℤ → AddSubgroup R.BdR) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) (χ : GQ l →* ℤ_[l]ˣ) (t : R.B)
    (hσ : ∀ x : ↥(MaximalUnramifiedExtension l), (x : Om l) ∈ K.1 → ((σ x : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1)
    (sB_mul : ∀ g h x, sB (g * h) x = sB g (sB h x)) (sB_one : ∀ x, sB 1 x = x)
    (sD_mul : ∀ g h x, sD (g * h) x = sD g (sD h x)) (sD_one : ∀ x, sD 1 x = x)
    (sB_u : ∀ (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)), g (c : Om l) = (c' : Om l) →
      sB g (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) R.B c')
    (sD_o : ∀ (g : GQ l) (x : Om l), sD g (algebraMap (Om l) R.BdR x) = algebraMap (Om l) R.BdR (g x))
    (invB : ∀ b, (∀ g ∈ GK K, sB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ algebraMap ↥(MaximalUnramifiedExtension l) R.B c = b)
    (invD : ∀ b, (∀ g ∈ GK K, sD g b = b) → ∃ y ∈ K.1, algebraMap (Om l) R.BdR y = b)
    (φ_inj : Function.Injective φ)
    (φ_u : ∀ c, φ (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) R.B (σ c))
    (φ_comm : ∀ g b, φ (sB g b) = sB g (φ b))
    (ι_u : ∀ c : ↥(MaximalUnramifiedExtension l), ι (algebraMap ↥(MaximalUnramifiedExtension l) R.B c) = algebraMap (Om l) R.BdR (c : Om l))
    (ι_inj : Function.Injective ι) (ι_comm : ∀ g b, ι (sB g b) = sD g (ι b))
    (F_o : ∀ x : Om l, algebraMap (Om l) R.BdR x ∈ F 0)
    (F_anti : ∀ a, F (a + 1) ≤ F a)
    (F_mul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (F_exh : ∀ x, ∃ a, x ∈ F a) (F_sep : ∀ x, (∀ a, x ∈ F a) → x = 0)
    (F_G : ∀ g a x, x ∈ F a → sD g x ∈ F a)
    (t_unit : IsUnit t)
    (t_act : ∀ g, sB g t = algebraMap ℚ_[l] R.B ((χ g : ℤ_[l]) : ℚ_[l]) * t)
    (t_φ : φ t = (l : R.B) * t) (t1 : ι t ∈ F 1) (t2 : ι t ∉ F 2)
    (fund : ∀ b, φ b = b → ι b ∈ F 0 → ∃ c : ℚ_[l], algebraMap ℚ_[l] R.B c = b) :
    ∃ PD : WeaklyAdmissibleFiltrations.PeriodData ↥(GK K) ℚ_[l] ↥(K0 K) ↥K.1 R.B R.BdR,
      PD.p = l ∧ (∀ g b, PD.actB g b = sB g b) ∧ (∀ g b, PD.actdR g b = sD g b) ∧ (∀ b, PD.φ b = φ b) ∧
      (∀ b, PD.ι b = ι b) ∧ PD.t = t ∧ (∀ g, ((PD.χ g : ℚ_[l]ˣ) : ℚ_[l]) = ((χ (g : GQ l) : ℤ_[l]) : ℚ_[l])) ∧
      (∀ a x, x ∈ PD.Fil a ↔ x ∈ F a) ∧
      ∀ (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) = (x : Om l) →
        ((PD.σ x : ↥(K0 K)) : Om l) = ((σ c : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have aB : ∀ c : ↥(K0 K), algebraMap ↥(K0 K) R.B c = algebraMap ↥(MaximalUnramifiedExtension l) R.B (inc K c) := fun _ => rfl
  have aD : ∀ c : ↥K.1, algebraMap ↥K.1 R.BdR c = algebraMap (Om l) R.BdR (c : Om l) := fun _ => rfl
  have aD0 : ∀ c : ↥(K0 K), algebraMap ↥(K0 K) R.BdR c = algebraMap (Om l) R.BdR (c : Om l) := fun _ => rfl
  have aQ : ∀ c : ℚ_[l], algebraMap ℚ_[l] R.B c = algebraMap ↥(MaximalUnramifiedExtension l) R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) :=
    fun c => IsScalarTower.algebraMap_apply _ _ _ c
  haveI := finiteDimensional_maxUnramifiedSubfield K
  refine ⟨{
    p := l
    hp := Fact.out
    finK₀ := finiteDimensional_maxUnramifiedSubfield K
    finK := K.2
    σ := sigK K σ hσ
    σ_bij := AlgHom.bijective _
    actB := actOf (fun g : ↥(GK K) => sB g) (fun g h x => sB_mul g h x) (fun x => sB_one x)
      (fun g c => by rw [aB]; exact sB_u g _ _ (fix K g _ c.2.1))
    invB := fun b hb => by
      obtain ⟨c, hc, e⟩ := invB b fun g hg => hb ⟨g, hg⟩
      exact ⟨⟨c, hc, c.2⟩, e⟩
    φ := AlgHom.mk φ fun c => by
      change φ _ = _
      rw [aQ, φ_u, AlgHom.commutes]
    φ_inj := φ_inj
    φ_K₀ := fun c => by
      change φ _ = _
      rw [aB, aB, φ_u, inc_sigK]
    φ_comm := fun g b => φ_comm g b
    actdR := actOf (fun g : ↥(GK K) => sD g) (fun g h x => sD_mul g h x) (fun x => sD_one x)
      (fun g c => by rw [aD, sD_o, fix K g _ c.2])
    invdR := fun b hb => by
      obtain ⟨c, hc, e⟩ := invD b fun g hg => hb ⟨g, hg⟩
      exact ⟨⟨c, hc⟩, e⟩
    ι := AlgHom.mk ι fun c => by
      change ι _ = _
      rw [aB, aD0, ι_u, inc_coe]
    ι_inj := ι_inj
    ι_comm := fun g b => ι_comm g b
    Fil := fun a =>
      { carrier := F a
        add_mem' := fun hx hy => (F a).add_mem hx hy
        zero_mem' := (F a).zero_mem
        smul_mem' := fun c x hx => by
          have := F_mul 0 a _ _ (F_o (c : Om l)) hx
          rw [zero_add, ← aD, ← Algebra.smul_def] at this
          exact this }
    Fil_anti := fun a x hx => F_anti a hx
    one_mem := by
      have := F_o 1
      rw [map_one] at this
      exact this
    Fil_mul := F_mul
    Fil_exh := F_exh
    Fil_sep := F_sep
    Fil_G := fun g a x hx => F_G g a x hx
    χ := ((Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp χ).comp (GK K).subtype
    t := t
    t_unit := t_unit
    t_act := fun g => by
      rw [Algebra.smul_def]
      exact t_act g
    t_φ := by
      rw [Algebra.smul_def, map_natCast]
      exact t_φ
    mem_filtration_one := t1
    not_mem_filtration_two := t2
    fund := fund }, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl,
    fun _ _ => Iff.rfl, fun x c h => ?_⟩
  have : inc K x = c := Subtype.ext h.symm
  rw [← this]
  rfl

theorem exists_realPD : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l), ∃ PD, IsRealPD C K PD := by
  intro l _ C K
  obtain ⟨a1, a2, a3, a4, a5, -, -, -, -, a10, -, a12, a13⟩ := ActLaws.act_laws l
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := _root_.GlobalTheory.MemLoc.filD_laws l
  obtain ⟨u1, u2, -, u4, u5, -⟩ := GlobalTheory.T.localPeriodRingsData_unramified_laws l C
  obtain ⟨t1, t2, t3, -⟩ := _root_.GlobalTheory.MemLoc.core_t_unit_fil l C
  have hσ := (frob_laws l C.σ C.σ_root).2.1 K
  have so := (_root_.GlobalTheory.MemLoc.SecUniq.main l C.o C.o_sec).2.2
  have sD_o : ∀ (g : GQ l) (x : Om l), Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) (C.o x)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o (g x)) := fun g x => by rw [a10, so]
  have F_o : ∀ x : Om l, algebraMap (Per.BdRp l) (Per.BdR l) (C.o x) ∈ Per.FilD l 0 := fun x => by
    have h1 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := (f7 0 1).1 (by rw [map_one]; exact f2)
    have h2 : C.o x * 1 ∈ Per.FilP l 0 := Ideal.mul_mem_left _ _ h1
    rw [mul_one] at h2
    exact (f7 0 _).2 h2
  have u_z : ∀ z : ℤ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) =
      algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z)) := fun z => by
    apply u4
    have e1 : ((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l]) : ↥(MaximalUnramifiedExtension l)) : Om l) = algebraMap ℚ_[l] (Om l) (z : ℚ_[l]) :=
      (IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) (Om l) (z : ℚ_[l])).symm
    rw [C.ι_u, C.ι_j, ULaws.alg_acris, C.j_cris.on0, e1, C.o_sec.z, Subalgebra.coe_algebraMap, aDp,
      RingHom.comp_apply]
  have t_act : ∀ g : GQ l, Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) C.t) =
      C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) ((C.χ g : ℤ_[l]) : ℚ_[l])) * algebraMap (Per.Acris l) (Per.Bcris l) C.t :=
    fun g => by
      rw [a12, _root_.GlobalTheory.MemLoc.TAct.t_act l C g, map_mul, u_z]
  have t_φ : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) C.t) =
      (l : Per.Bcris l) * algebraMap (Per.Acris l) (Per.Bcris l) C.t := by
    rw [a13, _root_.GlobalTheory.MemLoc.TPhi.t_phi l C, map_mul, map_natCast]
  have s1 : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∈ Per.FilD l 1 := by
    rw [C.ι_j]
    exact (f7 1 _).2 t2
  have s2 : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∉ Per.FilD l 2 := by
    rw [C.ι_j]
    exact fun h => t3 ((f7 2 _).1 h)
  obtain ⟨PD, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_abstract (ringsOf C) K
    (fun g => Per.σB g) (fun g => Per.σD g) (Per.φB l) C.ι (fun a => (Per.FilD l a).toAddSubgroup) C.σ C.χ
    (algebraMap (Per.Acris l) (Per.Bcris l) C.t) hσ a1 a2 a3 a4 u2 sD_o
    (InvCris.invariants_Bcris l C K) (GlobalTheory.T.bdR_galois_invariants_eq_finExt l C K) (_root_.GlobalTheory.MemLoc.phiB_injective l) u1 (fun g b => a5 g b) C.ι_u u4 u5
    F_o f1 f3 f4 f5 f6 t1 t_act t_φ s1 s2 (GlobalTheory.T.bcris_frobenius_fixed_fil_zero_eq_qp l C)
  exact ⟨PD, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end GlobalTheory.MemLoc.PdEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreLawsForReplacedHeckeCharacters
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

section Change

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] {σ : K →+* ℂ} {V : HSp D}
  {X : Comp → Data E r} {rd : C →ₛₗ[σ] FDSec X} {dict : GA D V → Σ c, Frame (X c).Ψ r} {mu mu' : GA D V → ℂ}

theorem norm_jFn_eq_of_muUnit (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (f : C) (q : AutQ V) :
    ‖jFn V σ rd dict mu' f q‖ = ‖jFn V σ rd dict mu f q‖ := by
  show ‖mu' q.out * rd f (dict q.out).1 (dict q.out).2‖ = ‖mu q.out * rd f (dict q.out).1 (dict q.out).2‖
  rw [norm_mul, norm_mul, h.2.1, h'.2.1]

theorem jMemL2_of_muUnit (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (hc : Continuous mu)
    (hc' : Continuous mu') (hL : JMemL2 V σ rd dict mu) : JMemL2 V σ rd dict mu' := by
  intro f
  have hne : ∀ g, mu g ≠ 0 := fun g h0 => by
    have := h.2.1 g
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hinv : ∀ γ ∈ GQ V, ∀ g, (fun g => mu' g / mu g) (γ * g) = (fun g => mu' g / mu g) g := by
    intro γ hγ g
    show mu' (γ * g) / mu (γ * g) = mu' g / mu g
    rw [h.1, h'.1, h.2.2.1 γ hγ, h'.2.2.1 γ hγ, one_mul, one_mul]
  have hm : AEStronglyMeasurable (onQ V (fun g => mu' g / mu g)) (muQ1 V) := by
    haveI : BorelSpace (GA D V) := ⟨rfl⟩
    rw [onQ_eq_lift _ hinv]
    refine Measurable.aestronglyMeasurable ?_
    exact measurable_from_quotient.2 (hc'.div hc hne).measurable
  have he : jFn V σ rd dict mu' f = onQ V (fun g => mu' g / mu g) * jFn V σ rd dict mu f := by
    funext q
    show mu' q.out * rd f (dict q.out).1 (dict q.out).2 =
      mu' q.out / mu q.out * (mu q.out * rd f (dict q.out).1 (dict q.out).2)
    rw [← mul_assoc, div_mul_cancel₀ _ (hne _)]
  refine (hL f).congr_norm ?_ (Filter.Eventually.of_forall fun q => (norm_jFn_eq_of_muUnit h h' f q).symm)
  rw [he]
  exact hm.mul (hL f).aestronglyMeasurable

theorem peterson_norm_independent_of_unitary_character (h : MuUnit V dict mu) (h' : MuUnit V dict mu') (hL : JMemL2 V σ rd dict mu)
    (hL' : JMemL2 V σ rd dict mu') (f : C) : l2NormAlt V σ rd dict mu' hL' f = l2NormAlt V σ rd dict mu hL f := by
  show ‖(hL' f).toLp _‖ = ‖(hL f).toLp _‖
  rw [Lp.norm_toLp, Lp.norm_toLp,
    eLpNorm_congr_norm_ae (hL' f).aestronglyMeasurable (hL f).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => norm_jFn_eq_of_muUnit h h' f q)]

end Change

theorem exists_mu_reCore : ∀ (D : D7) (T : CoreJ D) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), LawsJ T → LawsCore T.toCore → (∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ)) → ∃ mu, LawsJ (reCore T T.dict mu chiW T.x₀ T.cE) ∧ LawsCore (reCore T T.dict mu chiW T.x₀ T.cE).toCore := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro D T chiW hJ hC hchi
    have hex : ∀ j σ, ∃ mu : GA D (T.V j σ) → ℂ, InR D j → GoodEmb T.Q.c σ →
        MuVal (T.V j σ) (chiW j σ) mu ∧ MuUnit (T.V j σ) (T.dict j σ) mu ∧ Continuous mu := by
      intro j σ
      by_cases h : InR D j ∧ GoodEmb T.Q.c σ
      · obtain ⟨mu, h1, h2, h3, h4, h5⟩ := GlobalTheory.Member.exists_muVal D (T.V j σ) (chiW j σ) (hchi j h.1 σ h.2).1
          (hchi j h.1 σ h.2).2.1
        exact ⟨mu, fun hj hσ => ⟨h1, ⟨h2, h3, h4, (hJ.muUnit j hj σ hσ).2.2.2⟩, h5⟩⟩
      · exact ⟨fun _ => 1, fun hj hσ => absurd ⟨hj, hσ⟩ h⟩
    choose mu hmu using hex
    have hL : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CuspL2 (T.U j) σ (T.V j σ) (T.dict j σ) (mu j σ) :=
      fun j hj σ hσ a n hd => jMemL2_of_muUnit (hJ.muUnit j hj σ hσ) (hmu j σ hj hσ).2.1 (hJ.muCont j hj σ hσ)
        (hmu j σ hj hσ).2.2 (hJ.cuspidalL2Subspace j hj σ hσ a n hd)
    have hLM : LawsM (reCore T T.dict mu chiW T.x₀ T.cE).toCore :=
      { pins := hJ.pins
        half := hJ.half
        evalWD := hJ.evalWD
        unf := hJ.unf
        unTest := hJ.unTest
        chiTriv := hJ.chiTriv
        dictU := hJ.dictU
        spaceW := hJ.spaceW
        levelK := hJ.levelK
        xiAbs := hJ.xiAbs
        muUnit := fun j hj σ hσ => (hmu j σ hj hσ).2.1
        muCont := fun j hj σ hσ => (hmu j σ hj hσ).2.2
        finVol := hJ.finVol
        cuspFD := hJ.cuspFD
        supDef := hJ.supDef
        cuspidalL2Subspace := hL
        l2Def := fun j hj σ hσ a n hd f h0 => hJ.l2Def j hj σ hσ a n hd f
          ((peterson_norm_independent_of_unitary_character (hJ.muUnit j hj σ hσ) (hmu j σ hj hσ).2.1 (hJ.cuspidalL2Subspace j hj σ hσ a n hd)
            (hL j hj σ hσ a n hd) f).symm.trans h0)
        unitIndep := hJ.unitIndep
        ptNe := hJ.ptNe }
    refine ⟨mu, ?_, ?_⟩
    · exact
        { toLawsM := hLM
          cUnit := hJ.cUnit
          muVal := fun j hj σ hσ => (hmu j σ hj hσ).1
          muConj := fun j hj σ hσ => (hchi j hj σ hσ).2.2
          intAll := hJ.intAll
          modelW := hJ.modelW
          familyUniformisationBasePointOrthogonal := hJ.familyUniformisationBasePointOrthogonal
          kfHalf := hJ.kfHalf
          adPin := hJ.adPin }
    · exact
        { toLawsM := hLM
          cuspMul := hC.cuspMul
          latZ := hC.latZ
          cuNe := hC.cuNe
          expo := hC.expo }

end GlobalTheory.RealGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteUnitaryInfinitePointOfUnitaryFamil
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.InfSurj

theorem list_prod_single {G ι : Type} [Monoid G] [DecidableEq ι] (v : ι) (a : G) :
    ∀ l : List ι, l.Nodup → v ∈ l → (l.map fun u => if u = v then a else 1).prod = a
  | [], _, h => absurd h List.not_mem_nil
  | u :: l, hn, h => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.prod_cons]
    by_cases hu : u = v
    · subst hu
      have : (l.map fun w => if w = u then a else 1) = l.map fun _ => 1 :=
        List.map_congr_left fun w hw => if_neg fun (e : w = u) => hn.1 (e ▸ hw)
      rw [if_pos rfl, this, List.prod_map_one, mul_one]
    · rw [if_neg hu, one_mul]
      exact list_prod_single v a l hn.2 ((List.mem_cons.1 h).resolve_left (Ne.symm hu))

end GlobalTheory.InfSurj

theorem GlobalTheory.InfSurj.exists_infU_cAll_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : InfinitePlace E → GL (Fin n) ℂ), (∀ v, ((g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ x ∈ infU E n, cAll x = g := by
  intro E _ _ _ n g hg
  classical
  have he := fun v : InfinitePlace E => GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n v.embedding
  choose e he using he
  let y : InfinitePlace E → UA E n := fun v => ((e v).symm ⟨(g v : Matrix (Fin n) (Fin n) ℂ), hg v⟩ : embU n v.embedding)
  have hy : ∀ v, y v ∈ embU n v.embedding := fun v => ((e v).symm _).2
  have hyv : ∀ v, cEmb v.embedding (y v) = g v := fun v => by
    rw [← he v, ContinuousMulEquiv.apply_symm_apply]
    ext i j
    rfl
  have hyu : ∀ u v, u ≠ v → cEmb v.embedding (y u) = 1 := fun u v huv => by
    have h := (Subgroup.mem_inf.1 (hy u)).2
    rw [Subgroup.mem_iInf] at h
    have h2 := h v.embedding
    rw [Subgroup.mem_iInf] at h2
    exact h2 (by rw [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding]; exact Ne.symm huv)
  refine ⟨(Finset.univ.toList.map y).prod, ?_, ?_⟩
  · refine (infU E n).list_prod_mem fun z hz => ?_
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hz
    exact (Subgroup.mem_inf.1 (hy u)).1
  · funext v
    change cEmb v.embedding _ = g v
    rw [map_list_prod, List.map_map]
    have : (Finset.univ.toList.map (cEmb v.embedding ∘ y)) = Finset.univ.toList.map fun u => if u = v then g v else 1 :=
      List.map_congr_left fun u _ => by
        by_cases h : u = v
        · subst h; simp [hyv]
        · simp [h, hyu u v h]
    rw [this]
    exact GlobalTheory.InfSurj.list_prod_single v (g v) _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ v))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUMulInfU
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem exists_finU_mul_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : UA E n),
    ∃ k ∈ finU (E := E) (n := n), ∃ x ∈ infU E n, g = k * x := by
  intro E _ _ _ n g
  let k : UA E n := ⟨finGL E n (GeneralLinearGroup.map (pFin E) g.1), ClassFin.finGL_mem_UA _ (ClassFin.cT_pFin g)⟩
  have hk : k ∈ finU (E := E) (n := n) := pInf_finGL _
  refine ⟨k, hk, k⁻¹ * g, ?_, (mul_inv_cancel_left k g).symm⟩
  change GeneralLinearGroup.map (pFin E) (k⁻¹ * g).1 = 1
  have h : GeneralLinearGroup.map (pFin E) k.1 = GeneralLinearGroup.map (pFin E) g.1 := pFin_finGL _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, inv_mul_cancel]

end GlobalTheory.DefU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetOfKer
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RefCharValues

theorem sign_zpow_even (z : ℂ) (h : z ≠ 0) (k : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * k) = (z / starRingEnd ℂ z) ^ k := by
  rw [zpow_mul]
  congr 1
  have h1 : (‖z‖ : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using h
  rw [zpow_ofNat, div_pow, h1]
  field_simp

end GlobalTheory.RefCharValues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKsOfFinExt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem finiteDimensional_Ks_of_finExt {l : ℕ} [Fact l.Prime] (K : FinExt l) (s : ℕ) :
    FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have h0 : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  have hfin : Finite ↥{x : Om l | x ^ (l ^ s) = 1} := by
    apply Set.Finite.to_subtype
    refine (Multiset.finite_toSet (Polynomial.nthRoots (l ^ s) (1 : Om l))).subset ?_
    intro x hx
    exact (Polynomial.mem_nthRoots hpos).2 hx
  have h1 : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  unfold Ks
  exact IntermediateField.finiteDimensional_sup _ _

end GlobalTheory.MemLoc
end

