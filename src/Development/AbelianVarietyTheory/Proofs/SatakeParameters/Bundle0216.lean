module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInner
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicIsogenyConstantOfIsogenyFormula
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSph

def Gv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside {v} x}
  mul_mem' := fun hx hy => GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
  one_mem' := by
    intro u _
    exact Matrix.map_one _ (map_zero _) (map_one _)
  inv_mem' := fun hx => GlobalTheory.SatInd.CosetFin.trivOutside_inv hx

def Kv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) :=
  Umax L n ⊓ Gv L n v

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    TrivOutside T (1 : GAf L n) := by
  intro u _
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem commute_of_trivOutside (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n)
    (hx : TrivOutside {v} x) (hy : TrivOutside {v}ᶜ y) : Commute x y := by
  show x * y = y * x
  apply Subtype.ext; apply Units.ext
  change (((x * y : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
    (((y * x : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
  apply GlobalTheory.SplitAdelic.mat_ext
  intro u
  rw [GlobalTheory.SplitAdelic.mul_coe, GlobalTheory.SplitAdelic.mul_coe, Matrix.map_mul, Matrix.map_mul]
  obtain rfl | hu := eq_or_ne u v
  · rw [hy _ (by simp), mul_one, one_mul]
  · rw [hx u hu, mul_one, one_mul]

theorem heckeFunI_rt {W : Type} [AddCommGroup W] [Module ℂ W] (U : Subgroup (GAf L n))
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv : InertDatum L n v w) (h : Formalism.UG.GU Dv.σw n → ℂ) (φ : GAf L n → W) (b : GAf L n)
    (hb : TrivOutside {v}ᶜ b) :
    heckeFunI L n U Dv h (NG.rt L n b φ) = NG.rt L n b (heckeFunI L n U Dv h φ) := by
  funext g
  show heckeFunI L n U Dv h (NG.rt L n b φ) g = heckeFunI L n U Dv h φ (g * b)
  unfold heckeFunI
  refine finsum_congr fun c => ?_
  split_ifs with hc
  · show _ • φ (g * hc.choose * b) = _ • φ (g * b * hc.choose)
    rw [mul_assoc, mul_assoc, (commute_of_trivOutside v _ _ hc.choose_spec.2 hb).eq]
  · rfl

end GlobalTheory.InertSph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatePlaceCompletionIsoTame
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeBlockConj

theorem trivOutside_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

theorem trivOutside_inv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GA L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem rt_rt {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (a b : GAf L n) (f : GAf L n → W) (g : GAf L n) : NG.rt L n a (NG.rt L n b f) g = f (g * a * b) := rfl

end GlobalTheory.TypeBlockConj

namespace GlobalTheory.TypeBlockConj


end GlobalTheory.TypeBlockConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatesAutomorphicFormSpanFiniteDimensional
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.ConjSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def gen (t : (E →+* ℂ) × Fin n × Fin n) : infU E n → ℂ := fun x => (cEmb t.1 x.1).val t.2.1 t.2.2

def mono (l : List ((E →+* ℂ) × Fin n × Fin n)) : infU E n → ℂ := (l.map gen).prod


variable (E n) in
def polys (N : ℕ) : Submodule ℂ (infU E n → ℂ) :=
  Submodule.span ℂ (mono '' {l | l.length ≤ N})

theorem polys_fd (N : ℕ) : FiniteDimensional ℂ (polys E n N) :=
  FiniteDimensional.span_of_finite ℂ ((List.finite_length_le _ N).image _)

theorem polys_mono {N N' : ℕ} (h : N ≤ N') : polys E n N ≤ polys E n N' :=
  Submodule.span_mono (Set.image_mono fun _ hl => le_trans hl h)


variable (E n) in
abbrev gens : Set (infU E n → ℂ) := {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}

theorem exists_mono_of_mem_closure {f : infU E n → ℂ} (hf : f ∈ Submonoid.closure (gens E n)) :
    ∃ l, f = mono l := by
  induction hf using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ := hf
    exact ⟨[(τ, i, j)], by funext x; simp [mono, gen]⟩
  | one => exact ⟨[], by simp [mono]⟩
  | mul f g _ _ hf hg =>
    obtain ⟨l, rfl⟩ := hf
    obtain ⟨l', rfl⟩ := hg
    exact ⟨l ++ l', by simp [mono]⟩

theorem exists_polys_of_mem_adjoin {p : infU E n → ℂ} (hp : p ∈ Algebra.adjoin ℂ (gens E n)) :
    ∃ N, p ∈ polys E n N := by
  have h : p ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (gens E n)) := hp
  rw [Algebra.adjoin_eq_span] at h
  clear hp
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := exists_mono_of_mem_closure hf
    exact ⟨l.length, Submodule.subset_span ⟨l, (le_refl l.length : l.length ≤ l.length), rfl⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add f g _ _ hf hg =>
    obtain ⟨N, hN⟩ := hf
    obtain ⟨N', hN'⟩ := hg
    exact ⟨max N N', add_mem (polys_mono (le_max_left _ _) hN) (polys_mono (le_max_right _ _) hN')⟩
  | smul c f _ hf =>
    obtain ⟨N, hN⟩ := hf
    exact ⟨N, Submodule.smul_mem _ c hN⟩

theorem mono_mem_adjoin (l : List ((E →+* ℂ) × Fin n × Fin n)) : mono l ∈ Algebra.adjoin ℂ (gens E n) := by
  unfold mono
  induction l with
  | nil => simpa using one_mem (Algebra.adjoin ℂ (gens E n))
  | cons t l ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (Algebra.subset_adjoin ⟨t.1, t.2.1, t.2.2, rfl⟩) ih

theorem polys_le_adjoin (N : ℕ) : polys E n N ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (gens E n)) :=
  Submodule.span_le.2 (by rintro _ ⟨l, -, rfl⟩; exact mono_mem_adjoin l)

def conjIdx (σ : ℂ ≃+* ℂ) (t : (E →+* ℂ) × Fin n × Fin n) : (E →+* ℂ) × Fin n × Fin n :=
  (σ.toRingHom.comp t.1, t.2)

theorem mono_conj (σ : ℂ ≃+* ℂ) (l : List ((E →+* ℂ) × Fin n × Fin n)) {γ : UA E n} (hγ : γ ∈ ratU E n)
    (k : infU E n) (hk : cInf k.1 = cInf γ) : mono (l.map (conjIdx σ)) k = σ (mono l k) := by
  induction l with
  | nil => simp [mono]
  | cons t l ih =>
    simp only [mono, List.map_cons, List.prod_cons, Pi.mul_apply] at ih ⊢
    rw [ih, map_mul]
    congr 1
    obtain ⟨x, hx⟩ := exists_cEmb_entry_eq hγ hk t.2.1 t.2.2
    simp only [gen, conjIdx, hx]
    rfl

theorem exists_conj_polys (σ : ℂ ≃+* ℂ) {N : ℕ} {p : infU E n → ℂ} (hp : p ∈ polys E n N) :
    ∃ p' ∈ polys E n N, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, hl, rfl⟩ := hf
    exact ⟨mono (l.map (conjIdx σ)), Submodule.subset_span ⟨_, by simpa using hl, rfl⟩,
      fun γ hγ k hk => mono_conj σ l hγ k hk⟩
  | zero => exact ⟨0, zero_mem _, fun _ _ _ _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    exact ⟨f' + g', add_mem hf' hg', fun γ hγ k hk => by
      rw [Pi.add_apply, Pi.add_apply, map_add (f := _), hf γ hγ k hk, hg γ hγ k hk]⟩
  | smul c f _ hf =>
    obtain ⟨f', hf', hf⟩ := hf
    exact ⟨σ c • f', Submodule.smul_mem _ _ hf', fun γ hγ k hk => by
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hf γ hγ k hk]⟩

theorem conj_span_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ),
    IsAutFormU φ → ∃ M : Submodule ℂ (UA E n → ℂ), FiniteDimensional ℂ M ∧ ∀ (σ : ℂ ≃+* ℂ) (φ' : UA E n → ℂ),
      IsAutFormU φ' → (∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g)) → φ' ∈ M := by
  intro E _ _ _ n φ hφ
  classical
  obtain ⟨hdense, hdk, -, a, b, -, -, hab, -⟩ := GlobalTheory.UnitarySplit.dense_and_split E n
  obtain ⟨m, p, e, hpe, hdec⟩ := GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm E n φ hφ
  have hcont := (GlobalTheory.PolyRealU.poly_infU E n).1
  choose D hD using fun i => exists_polys_of_mem_adjoin (hpe i).1
  set N := Finset.univ.sup D with hN
  have hpN : ∀ i, p i ∈ polys E n N := fun i => polys_mono (Finset.le_sup (Finset.mem_univ i)) (hD i)
  set K := GlobalTheory.UnitaryDecomp.finStab φ with hK
  obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hφ.level
  set S' : Finset (UA E n) := S.image fun s => ((a s : finU (E := E) (n := n)) : UA E n) with hS'
  let M : Submodule ℂ (UA E n → ℂ) :=
    { carrier := {ψ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ K, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧
        ∀ s ∈ S', (fun x : infU E n => ψ (s * x)) ∈ polys E n N}
      add_mem' := fun {ψ χ} hψ hχ =>
        ⟨fun γ hγ g => by simp only [Pi.add_apply, hψ.1 γ hγ g, hχ.1 γ hγ g],
          fun k hk g => by simp only [Pi.add_apply, hψ.2.1 k hk g, hχ.2.1 k hk g],
          fun s hs => add_mem (hψ.2.2 s hs) (hχ.2.2 s hs)⟩
      zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => zero_mem _⟩
      smul_mem' := fun c ψ hψ =>
        ⟨fun γ hγ g => by simp only [Pi.smul_apply, hψ.1 γ hγ g],
          fun k hk g => by simp only [Pi.smul_apply, hψ.2.1 k hk g],
          fun s hs => Submodule.smul_mem _ c (hψ.2.2 s hs)⟩ }

  have hred : ∀ g : UA E n, ∃ s ∈ S', ∃ y : infU E n, ∀ ψ ∈ M, ψ g = ψ (s * y) := by
    intro g
    obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
    refine ⟨((a s : finU (E := E) (n := n)) : UA E n), by rw [hS']; exact Finset.mem_image_of_mem _ hs, ⟨(b s).1 * x, mul_mem (b s).2 hx⟩, fun ψ hψ => ?_⟩
    rw [hψ.2.1 k hk, mul_assoc, hψ.1 γ hγ]
    conv_lhs => rw [hab s]
    simp only [mul_assoc]
  haveI := polys_fd (E := E) (n := n) N
  let f : M →ₗ[ℂ] ((s : S') → polys E n N) :=
    { toFun := fun ψ s => ⟨fun x => ψ.1 (s.1 * x), ψ.2.2.2 s.1 s.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective f := by
    intro ψ χ h
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨s, hs, y, hy⟩ := hred g
    rw [hy ψ.1 ψ.2, hy χ.1 χ.2]
    exact congrFun (congrArg Subtype.val (congrFun h ⟨s, hs⟩)) y
  refine ⟨M, Module.Finite.of_injective f hinj, fun σ φ' hφ' hagree => ?_⟩

  have hrat : ∀ s ∈ finU (E := E) (n := n), ∀ k : infU E n, ∀ γ ∈ ratU E n, cInf k.1 = cInf γ →
      φ' (s * (k : UA E n)) = σ (φ (s * (k : UA E n))) := by
    intro s hs k γ hγ hk
    have hy : γ⁻¹ * (s * (k : UA E n)) ∈ finU (E := E) (n := n) := by
      have hs1 : cInf s = 1 := hs
      show cInf (γ⁻¹ * (s * (k : UA E n))) = 1
      rw [map_mul, map_mul, map_inv, hs1, hk, one_mul, inv_mul_cancel]
    have e1 : s * (k : UA E n) = γ * (γ⁻¹ * (s * (k : UA E n))) := by group
    rw [e1, hφ'.left γ hγ, hφ.left γ hγ, hagree _ hy]
  refine ⟨hφ'.left, fun k hk => ?_, fun s hs => ?_⟩
  ·
    have hkφ : ∀ x, φ (x * (k : UA E n)) = φ x := fun x => congrFun hk x
    refine congrFun (Continuous.ext_on hdense (hφ'.cont.comp (continuous_mul_const _)) hφ'.cont ?_)
    rintro _ ⟨γ, hγ, x, hx, rfl⟩
    have hxk : x * (k : UA E n) ∈ finU (E := E) (n := n) := mul_mem hx k.2
    simp only [Function.comp_apply]
    rw [mul_assoc, hφ'.left γ hγ, hφ'.left γ hγ, hagree _ hxk, hagree _ hx, hkφ]
  · obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.1 hs
    have hsf : ((a s₀ : finU (E := E) (n := n)) : UA E n) ∈ finU (E := E) (n := n) := (a s₀).2
    choose p' hp'm hp' using fun i => exists_conj_polys σ (hpN i)
    have hq : (∑ i, σ (e i (a s₀)) • p' i) ∈ polys E n N :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hp'm i)
    convert hq using 1
    refine Continuous.ext_on hdk (hφ'.cont.comp (continuous_const.mul continuous_subtype_val))
      (hcont _ (polys_le_adjoin N hq)) ?_
    rintro k ⟨γ, hγ, hk⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hrat _ hsf k γ hγ hk, hdec k, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hp' i γ hγ k hk, mul_comm]

end GlobalTheory.ConjSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveLatticeSigmaTwoAlgebraicOfInvariantsAlgebra
section
noncomputable section

namespace GlobalTheory.CurveSigmaAlg

open NumberField Formalism.BasicNotions GlobalTheory.IsogConst

theorem hasCMBy_curve (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (L : PeriodPair)
    (hL : L.lattice.toAddSubgroup = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
  have hδ0 : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  obtain ⟨-, hCM⟩ := GlobalTheory.InertGenusOne.lamOf_lat D cc δ hcc.1 hδ0
  intro ω hω
  have h1 := hCM ω (by rw [← hL]; exact hω)
  rw [← hL] at h1
  have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
    unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
  rw [e]; exact h1

theorem secondEisensteinAlgebraic_of_invAlg : Formalism.L2.KerInert.Sigma.InvAlg → Formalism.L2.KerInert.Sigma.SecondEisensteinAlgebraic := by
  intro hInv D cc δ hcc hδ L hL
  obtain ⟨h2, h3⟩ := hInv D cc δ hcc hδ L hL
  have hcm := hasCMBy_curve D cc δ hcc hδ L hL
  have hd0 : 0 < D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).pos
  obtain ⟨S, -, -, hIso, -⟩ := Formalism.L2.Th1.F.hasCMByIsogeny D.host.d L hcm (-1) 2 (by simp) hd0
  have hαsq := alpha_sq D.host.d
  have hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))
  have hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0 := by
    intro h0
    rw [h0] at hαsq
    have : (D.host.d : ℂ) = 0 := by linear_combination hαsq
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have he : InQ (Formalism.L2.Th1.F.pSeries L) := by
    intro k
    rw [Formalism.L2.KerInert.AlgP.pSeries_eq_map Formalism.MainNotions.TaylorLogMetric.Qbar L h2 h3, PowerSeries.coeff_map]
    exact SetLike.coe_mem _
  have hc := algebraic_isogenyConstant_of_isogenyFormula _ he _ _ hα hα0 _ hIso
  rw [hαsq] at hc
  have hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) := by
    push_cast; ring
  rw [hN] at hc
  have hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card S + 1 + D.host.d ≠ 0)
  have e : Formalism.L2.Th1.F.s2 L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ *
      (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 L) := by
    rw [← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rw [e]
  exact mul_mem (inv_mem (natCast_mem _ _)) hc

end GlobalTheory.CurveSigmaAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryRationalHeckeCommuteComplexAutomoStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryRationalHecke_commute_complexAutomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ) (t : UA E n →₀ ℂ), (∀ g ∈ t.support, g ∈ finU (E := E) (n := n) ∧ ∃ q : ℚ, t g = q) → ∀ (φ φ' : UA E n → ℂ) (z : ℂ), IsAutFormU φ → IsAutFormU φ' → (∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g)) → opOf (RU E n) t φ = z • φ → opOf (RU E n) t φ' = σ z • φ' := by
  first | exact @GlobalTheory.EigenConj.opOf_conj | exact GlobalTheory.EigenConj.opOf_conj | (intros; apply GlobalTheory.EigenConj.opOf_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBalancedBilinearTensorProductMapStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_balancedBilinear_tensorProduct_map : ∀ {LL U D₁ D₂ D₃ : Type} [Field LL] [Field U] [AddCommGroup D₁] [Module LL D₁] [AddCommGroup D₂] [Module LL D₂] [AddCommGroup D₃] [Module LL D₃] (m₁ : U →+* Module.End LL D₁) (m₂ : U →+* Module.End LL D₂) (m₃ : U →+* Module.End LL D₃) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃), (∀ c x y, β (m₁ c x) y = m₃ c (β x y)) → (∀ c x y, β x (m₂ c y) = m₃ c (β x y)) → ∃ Φ : GlobalTheory.Pst.Letter m₁ F τ ⊗[F] GlobalTheory.Pst.Letter m₂ F τ →ₗ[F] GlobalTheory.Pst.Letter m₃ F τ, ∀ x y, Φ (GlobalTheory.Pst.letterMk m₁ F τ x ⊗ₜ GlobalTheory.Pst.letterMk m₂ F τ y) = GlobalTheory.Pst.letterMk m₃ F τ (β x y) := by
  first | exact @GlobalTheory.LetterDescent.exists_letter_tensor_map | exact GlobalTheory.LetterDescent.exists_letter_tensor_map | (intros; apply GlobalTheory.LetterDescent.exists_letter_tensor_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowUnitProof

theorem exists_splitPlace_eq (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  have hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun _ =>
    D.host.φ₀.injective (by
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])
  obtain ⟨x, hx, hy⟩ := hw
  have hc : IsSplitPl D.host (GlobalTheory.SplitConjPlace.conjPlE w) := by
    refine ⟨IsCMField.ringOfIntegersComplexConj D.host.E x, ?_, fun y hy' => ?_⟩
    · rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO]; exact hx
    · rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
      apply hy
      rw [hstar, IsCMField.coe_ringOfIntegersComplexConj, hy', hstar, IsCMField.coe_ringOfIntegersComplexConj,
        IsCMField.complexConj_apply_apply]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hc
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have h1 := hs (IsCMField.ringOfIntegersComplexConj D.host.E y) y (by
    rw [hstar, IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_apply_apply])
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO] at h1
  exact h1.symm

end GlobalTheory.RowUnitProof

namespace GlobalTheory.RowUnitProof

end GlobalTheory.RowUnitProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugationStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineParameter_invariant_under_conjugation : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (r r' : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)) (p : GL (Fin a) (Qbar l)), (∀ g, r' g = p * r g * p⁻¹) → IsPstAt P Bw r → IsPstAt P Bw r' ∧ wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  first | exact @GlobalTheory.PstConj.main | exact GlobalTheory.PstConj.main | (intros; apply GlobalTheory.PstConj.main <;> assumption)
end

