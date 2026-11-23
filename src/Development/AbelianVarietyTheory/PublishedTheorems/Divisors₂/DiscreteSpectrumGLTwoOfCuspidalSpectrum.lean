module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.DiscChar

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {ω χ : HChar E}
  {V : Submodule ℂ (Sm E a)}

structure IsDiscreteWith (ω : HChar E) (V : Submodule ℂ (Sm E a)) : Prop where
  aut : ∀ φ ∈ V, IsAutForm φ
  central : ∀ z : Neutral.B1.Ideles E, ∀ φ ∈ V,
    rt E a (GeneralLinearGroup.scalar (Fin a) z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ
  sqInt : ∀ φ ∈ V, IsSqInt fun g => ((‖φ.1 g‖ : ℝ) : ℂ)
  stable : _root_.GlobalTheory.CuspRep.IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, _root_.GlobalTheory.CuspRep.IsStable W → W = ⊥ ∨ W = V


variable (a) in
def detLine (χ : HChar E) : Submodule ℂ (Sm E a) := Submodule.span ℂ {mulChi a χ (oneFn E a)}

theorem chiDet_scalar (χ : HChar E) (z : Neutral.B1.Ideles E) :
    chiDet a χ (GeneralLinearGroup.scalar (Fin a) z) = (χ ^ a).1 z := by
  have : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin a) z) = z ^ a := Units.ext (by
    change (Matrix.scalar (Fin a) (z : Ad E)).det = _
    simp)
  exact (congrArg χ.1 this).trans ((map_pow _ _ _).trans (MonoidHom.pow_apply χ.1 a z).symm)

abbrev expId (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (t : ℝ) : Neutral.B1.Ideles E :=
  infId E (expU fun _ : InfinitePlace E => (t : ℂ))

theorem IsDiscreteWith.apply (h : IsDiscreteWith ω V) {φ : Sm E a} (hφ : φ ∈ V) (z : Neutral.B1.Ideles E) (g : GA E a) :
    φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g := by
  rw [CuspRep.scalar_comm]
  exact congrFun (congrArg Subtype.val (h.central z φ hφ)) g

theorem enorm_ofReal_norm (z : ℂ) : ‖((‖z‖ : ℝ) : ℂ)‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, Complex.norm_of_nonneg (norm_nonneg z), ofReal_norm]

theorem isDiscreteWith_of_isDiscrete (h : IsDiscrete V) (hc : ∀ z : Neutral.B1.Ideles E, ∀ φ ∈ V,
    rt E a (GeneralLinearGroup.scalar (Fin a) z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ) : IsDiscreteWith ω V :=
  ⟨h.aut, hc, fun φ hφ => ⟨fun t g => by simp only [(h.sqInt φ hφ).1 t g], by
    simpa only [enorm_ofReal_norm] using (h.sqInt φ hφ).2⟩, h.stable, h.ne_bot, h.irred⟩

theorem isSqInt_of_bounded {f : GA E a → ℂ} (h : ∀ t g, f (splitCentre E a t * g) = f g) {C : ℝ}
    (hC : ∀ g, ‖f g‖ ≤ C) : IsSqInt f := by
  have hd := isFundamentalDomain_stdDom (latticeGL E a) (Measure.haar : Measure (GA E a))
  have hf := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a Measure.haar
  refine ⟨h, Measure.haar, _, inferInstance, hd, ?_⟩
  refine (lintegral_mono (g := fun _ => ENNReal.ofReal C ^ 2) fun g => ?_).trans_lt ?_
  · exact pow_le_pow_left' ((ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_ofReal (hC g))) 2
  · rw [setLIntegral_const, ← quotMeasure_univ hd]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top _ _)

theorem IsDiscreteWith.twist (h : IsDiscreteWith ω V) {ν : HChar E} (hν : ν.IsUnitary) :
    IsDiscreteWith (ω * ν ^ a) (V.map (mulChi a ν).toLinearMap) := by
  constructor
  case aut =>
    rintro _ ⟨φ, hφ, rfl⟩
    exact (h.aut φ hφ).mulChi ν
  case central =>
    rintro z _ ⟨φ, hφ, rfl⟩
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (g * _) * (chiDet a ν (g * _) : ℂ) = ((ω.1 z * (ν ^ a).1 z : ℂˣ) : ℂ) * (φ.1 g * (chiDet a ν g : ℂ))
    rw [← CuspRep.scalar_comm, h.apply hφ, map_mul, chiDet_scalar, Units.val_mul, Units.val_mul]
    ring
  case sqInt =>
    rintro _ ⟨φ, hφ, rfl⟩
    convert h.sqInt φ hφ using 3 with g
    change ‖φ.1 g * (ν.1 _ : ℂ)‖ = _
    rw [norm_mul, hν, mul_one]
  case stable =>
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, add_mem (V.smul_mem _ (h.stable o φ hφ)) (V.smul_mem _ hφ), (act_mulChi ν o φ).symm⟩
  case ne_bot =>
    exact fun e => h.ne_bot ((Submodule.map_eq_bot_iff (e := mulChi a ν)).1 e)
  case irred =>
    intro W hW hs
    have h := h.irred (W.comap (mulChi a ν).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (mulChi a ν).injective h2]) fun o φ hφ => by
      have h1 : _ ∈ W.comap (mulChi a ν).toLinearMap := (act_mulChi ν o φ) ▸ hs o _ hφ
      exact (Submodule.smul_mem_iff _ (Units.ne_zero (opMul ν o))).1
        ((Submodule.add_mem_iff_left _ (Submodule.smul_mem _ _ hφ)).1 h1)
    have e := Submodule.map_comap_eq_of_surjective (f := (mulChi a ν).toLinearMap) (mulChi a ν).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem isDiscreteWith_detLine (hχ : χ.IsUnitary) : IsDiscreteWith (χ ^ a) (detLine a χ) := by
  have h1 : IsDiscreteWith 1 (Submodule.span ℂ {oneFn E a}) :=
    isDiscreteWith_of_isDiscrete ⟨fun _ => isAutForm_const, fun φ hφ => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
        exact isSqInt_of_bounded (f := fun _ => c * 1) (fun _ _ => rfl) fun _ => le_rfl,
      isStable_const, fun e => oneFn_ne_zero (Submodule.span_singleton_eq_bot.1 e),
      fun W hW _ => (nonzero_span_atom _ oneFn_ne_zero).le_iff.1 hW⟩ fun z φ hφ => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
        exact (one_smul ℂ _).symm
  have h2 := h1.twist hχ
  rwa [one_mul, Submodule.map_span, Set.image_singleton] at h2

theorem detLine_ne_cusp (ha : 1 < a) (χ : HChar E) (π : CuspSub E a) : detLine a χ ≠ π.V := fun e => by
  have h := (π.cusp _ (e.le (Submodule.mem_span_singleton_self _))).mulChi χ⁻¹
  rw [← mulChi_mul, mul_inv_cancel, mulChi_one] at h
  exact GlobalTheory.ConstNotCusp.not_isCuspidal_oneFn E a ha h.2

section Local

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.DiscChar

namespace GlobalTheory.Published

open GlobalTheory.DiscChar

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

end GlobalTheory.Published

end
