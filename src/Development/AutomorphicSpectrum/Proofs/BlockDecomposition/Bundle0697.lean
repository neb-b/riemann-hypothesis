module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0015
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0017
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0001
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0692
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

section Abstract

variable {A B : Type}

def prodSpan (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)) : Submodule ℂ (A × B → ℂ) :=
  Submodule.span ℂ {F | ∃ a ∈ U₁, ∃ b ∈ U₂, F = fun x => a x.1 * b x.2}

end Abstract

section Lin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N r s : ℕ}


variable (E) in
abbrev KO (n : ℕ) : Subgroup (GL (Fin n) (Af E)) := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n

def typeF (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) : Submodule ℂ (GA E N → ℂ) where
  carrier := {f | (∀ u ∈ K, ∀ g, f (g * finGL E N u) = f g) ∧
    ∀ g, (fun k : Kinf E N => f (g * infGL E N (Unitary.toUnits k))) ∈ W}
  add_mem' := fun {f f'} h h' => ⟨fun u hu g => by simp only [Pi.add_apply, h.1 u hu g, h'.1 u hu g],
    fun g => W.add_mem (h.2 g) (h'.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  smul_mem' := fun c f h => ⟨fun u hu g => by simp only [Pi.smul_apply, h.1 u hu g],
    fun g => W.smul_mem c (h.2 g)⟩

def typed (U : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) :
    Submodule ℂ (Sm E N) :=
  U ⊓ (typeF K W).comap (Sm E N).subtype

structure FlatFn (e : GA E N → ℂ) : Prop where
  ne : ∀ x, e x ≠ 0
  rinv : ∀ x (k : Kinf E N), ∀ c ∈ KO E N, e (x * cf N k c) = e x
  sm : e ∈ Sm E N

def Carries (e : GA E N → ℂ) (U U' : Submodule ℂ (Sm E N)) : Prop :=
  ∀ φ ∈ U, ∃ φ' ∈ U', ∀ x, φ'.1 x = e x * φ.1 x

def FinStable (U : Submodule ℂ (Sm E N)) : Prop := ∀ (g : GL (Fin N) (Af E)), ∀ φ ∈ U, act (.fin g) φ ∈ U

def indSpan (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)) : Submodule ℂ (Sm E (r + s)) :=
  Submodule.span ℂ {φ | MemInd2 U₁ U₂ φ}

theorem exists_iw (x : GA E (r + s)) : ∃ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
    (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) ∧ x = unip u * lev (Ad E) r s m * cf (r + s) k c := by
  obtain ⟨b, hb, k, hy⟩ := GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s)
    (GeneralLinearGroup.map (pInf E) x)
  have hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id := by
    letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  obtain ⟨xi, mi, hbi⟩ := IwaFin.exists_unip_mul_lev r s b
    (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
    (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
  obtain ⟨xf, mf, c, hc, hf⟩ := IwaFin.exists_unip_lev_integral E r s (GeneralLinearGroup.map (pFin E) x)
  have e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p := fun p => by
    rw [map_add (f := _), show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _,
      show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]
  have e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p := fun p => by
    rw [map_add (f := _), show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]
  refine ⟨fun p => sInf E (xi p) + sFin E (xf p),
    (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), k, c, hc, ga_ext ?_ ?_⟩
  · simp only [cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]
    rw [hy, hbi]
  · simp only [cf, map_mul, IwaAd.map_unip, IwaAd.map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hf]

def leviOf (x : GA E (r + s)) : GA E r × GA E s := (exists_iw x).choose_spec.choose

def nodeFn (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (x : GA E (r + s)) : ℂ := e₁ (leviOf x).1 * e₂ (leviOf x).2

def absFn (N : ℕ) (w : ℂ) (x : GA E N) : ℂ := (chiDet N (GlobalTheory.CuspRep.Model.absC E w) x : ℂˣ)

end Lin

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def typeHF (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) : Submodule ℂ (H E a b → ℂ) where
  carrier := {F | TypeH K₁ K₂ W₁ W₂ F}
  add_mem' := fun {F F'} h h' => ⟨fun u₁ hu₁ u₂ hu₂ x => by
      simp only [Pi.add_apply, h.1 u₁ hu₁ u₂ hu₂ x, h'.1 u₁ hu₁ u₂ hu₂ x],
    fun x => Submodule.add_mem _ (h.2 x) (h'.2 x)⟩
  zero_mem' := ⟨fun _ _ _ _ _ => rfl, fun _ => Submodule.zero_mem _⟩
  smul_mem' := fun c F h => ⟨fun u₁ hu₁ u₂ hu₂ x => by simp only [Pi.smul_apply, h.1 u₁ hu₁ u₂ hu₂ x],
    fun x => Submodule.smul_mem _ c (h.2 x)⟩

end Pair

end GlobalTheory.CompanionTheory.LimV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariant
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
open scoped RestrictedProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicUnimod

open GroundTheory.Automorphic

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem modularCharacter_eq_one_of_map (μ : Measure G) [μ.IsHaarMeasure] {z : G}
    (h : μ.map (fun x => x * z) = μ) : (Measure.modularCharacter z : ℝ≥0) = 1 := by
  have h1 := Measure.map_right_mul_eq_modularCharacterFun_smul μ z
  rw [h] at h1
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have h2 := congrArg (fun m : Measure G => m C) h1
  have hne : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC1).ne'
  have hnt : μ C ≠ ⊤ := hC.measure_lt_top.ne
  simp only [Measure.coe_nnreal_smul_apply] at h2
  have h3 : (Measure.modularCharacterFun z : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
  exact_mod_cast h3

theorem modularCharacter_eq_one_of_central (μ : Measure G) [μ.IsHaarMeasure] {z : G}
    (hz : ∀ h, z * h = h * z) : (Measure.modularCharacter z : ℝ≥0) = 1 := by
  refine modularCharacter_eq_one_of_map μ ?_
  rw [show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm,
    Measure.IsMulLeftInvariant.map_mul_left_eq_self]

theorem modularCharacter_eq_one_of_compact (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : (Measure.modularCharacter k : ℝ≥0) = 1 :=
  modularCharacter_eq_one_of_map μ
    (GlobalTheory.CompanionTheory.Xa1.map_mul_right_eq_of_mem_compact_subgroup G μ inferInstance inferInstance K hK k hk)

theorem isMulRightInvariant_of_modularCharacter (μ : Measure G) [μ.IsHaarMeasure]
    (h : ∀ g : G, (Measure.modularCharacter g : ℝ≥0) = 1) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    show Measure.modularCharacterFun g = 1 from h g, one_smul]

end General

section Products

theorem pi_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    (Δ : (∀ i, H i) →* ℝ≥0) (h : ∀ i (x : H i), Δ (Pi.mulSingle i x) = 1) (x : ∀ i, H i) :
    Δ x = 1 := by
  have key : ∀ (S : Finset ι) (x : ∀ i, H i), (∀ i, i ∉ S → x i = 1) → Δ x = 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx
      rw [show x = 1 from funext fun i => hx i (by simp), map_one]
    | insert a S _ ih =>
      intro x hx
      have e : x = (x * (Pi.mulSingle a (x a))⁻¹) * Pi.mulSingle a (x a) := by simp
      rw [e, map_mul, h, mul_one]
      refine ih _ fun i hi => ?_
      by_cases hia : i = a
      · subst hia
        simp
      · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hia, inv_one, mul_one]
        exact hx i (by simp [hia, hi])
  exact key Finset.univ x (by simp)

theorem restricted_eq_one {ι : Type*} [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    {A : ∀ i, Subgroup (H i)} (Δ : (Πʳ i, [H i, A i]) →* ℝ≥0)
    (h1 : ∀ i (x : H i), Δ (RestrictedProduct.mulSingle A i x) = 1)
    (h2 : ∀ x : Πʳ i, [H i, A i], (∀ i, x i ∈ A i) → Δ x = 1) (x : Πʳ i, [H i, A i]) :
    Δ x = 1 := by
  have key : ∀ (S : Finset ι) (x : Πʳ i, [H i, A i]), (∀ i, i ∉ S → x i ∈ A i) → Δ x = 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun x hx => h2 x fun i => hx i (by simp)
    | insert a S _ ih =>
      intro x hx
      have e : x = (x * (RestrictedProduct.mulSingle A a (x a))⁻¹) *
          RestrictedProduct.mulSingle A a (x a) := by simp
      rw [e, map_mul, h1, mul_one]
      refine ih _ fun i hi => ?_
      by_cases hia : i = a
      · subst hia
        simp [RestrictedProduct.mulSingle_eq_same, one_mem]
      · simp only [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
          RestrictedProduct.mulSingle_eq_of_ne A _ hia, inv_one, mul_one]
        exact hx i (by simp [hia, hi])
  have hfin : {i | x i ∉ A i}.Finite := x.2
  exact key hfin.toFinset x fun i hi => by simpa using hi

def singleHom {ι : Type*} [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    (A : ∀ i, Subgroup (H i)) (i : ι) : H i →* Πʳ i, [H i, A i] where
  toFun := RestrictedProduct.mulSingle A i
  map_one' := by
    ext j
    by_cases h : j = i
    · subst h; simp [RestrictedProduct.mulSingle_eq_same]
    · simp [RestrictedProduct.mulSingle_eq_of_ne A _ h]
  map_mul' x y := by
    ext j
    by_cases h : j = i
    · subst h; simp [RestrictedProduct.mulSingle_eq_same]
    · simp [RestrictedProduct.mulSingle_eq_of_ne A _ h]

end Products

section Adelic

variable (E : Type) [Field E] [NumberField E] (N : ℕ)

abbrev PInf : Type := ∀ w : InfinitePlace E, GL (Fin N) w.Completion

abbrev AInt (v : HeightOneSpectrum (𝓞 E)) : Subgroup (GL (Fin N) (v.adicCompletion E)) :=
  GLnLocal.integralGL (v.adicCompletion E) N

abbrev PFin : Type := Πʳ v : HeightOneSpectrum (𝓞 E), [GL (Fin N) (v.adicCompletion E), AInt E N v]


open GroundTheory.Automorphic.AdelicGLn in
def finInc : FiniteAdelicGL E N →* GA E N :=
  ((prodEquiv E N).symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)

open GroundTheory.Automorphic.AdelicGLn in
theorem continuous_finInc : Continuous (finInc E N) :=
  (prodEquiv E N).symm.continuous.comp (continuous_const.prodMk continuous_id)


open GroundTheory.Automorphic.AdelicGLn in
theorem isMulRightInvariant_GA (μ : Measure (GA E N)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  classical
  refine isMulRightInvariant_of_modularCharacter μ fun g => ?_
  let e := restrictedProductEquiv E N
  let Δ : PInf E N × PFin E N →* ℝ≥0 := (Measure.modularCharacter : GA E N →* ℝ≥0).comp e.symm.toMulEquiv.toMonoidHom
  have hΔ : ∀ z, Δ z = Measure.modularCharacter (e.symm z) := fun _ => rfl
  have hcen : ∀ z, (∀ h, z * h = h * z) → Δ z = 1 := fun z hz => by
    rw [hΔ]
    refine modularCharacter_eq_one_of_central μ fun h => ?_
    have := hz (e h)
    apply e.injective
    simpa [map_mul] using this
  have hinf : ∀ (w : InfinitePlace E) (x : GL (Fin N) w.Completion),
      Δ (Pi.mulSingle w x, 1) = 1 := fun w x => by
    let ι : GL (Fin N) w.Completion →* PInf E N × PFin E N :=
      (MonoidHom.inl (PInf E N) (PFin E N)).comp (MonoidHom.mulSingle (fun w : InfinitePlace E => GL (Fin N) w.Completion) w)
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center (Δ.comp ι) (fun c hc => hcen _ fun h => ?_) x
    refine Prod.ext (funext fun u => ?_) (by simp [ι])
    by_cases hu : u = w
    · subst hu
      simpa [ι] using hc (h.1 u)
    · simp [ι, Pi.mulSingle_eq_of_ne hu]
  have hfin : ∀ (v : HeightOneSpectrum (𝓞 E)) (x : GL (Fin N) (v.adicCompletion E)),
      Δ (1, RestrictedProduct.mulSingle (AInt E N) v x) = 1 := fun v x => by
    let ι : GL (Fin N) (v.adicCompletion E) →* PInf E N × PFin E N :=
      (MonoidHom.inr (PInf E N) (PFin E N)).comp (singleHom (AInt E N) v)
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center (Δ.comp ι) (fun c hc => hcen _ fun h => ?_) x
    refine Prod.ext (by simp [ι]) ?_
    ext u : 1
    by_cases hu : u = v
    · subst hu
      simpa [ι, singleHom, RestrictedProduct.mulSingle_eq_same] using hc (h.2 u)
    · simp [ι, singleHom, RestrictedProduct.mulSingle_eq_of_ne _ _ hu]
  have hint : ∀ b : PFin E N, (∀ v, b v ∈ AInt E N v) → Δ (1, b) = 1 := fun b hb => by
    have hk : (finiteRestrictedEquiv E N).symm b ∈ integralFiniteGL E N :=
      (mem_integralFiniteGL_iff_forall E N).2 (by simpa using hb)
    have hcomp : IsCompact (((integralFiniteGL E N).map (finInc E N) : Subgroup (GA E N)) : Set (GA E N)) := by
      rw [Subgroup.coe_map]
      exact (isCompact_integralFiniteGL E N).image (continuous_finInc E N)
    have he : e.symm (1, b) = finInc E N ((finiteRestrictedEquiv E N).symm b) := by
      apply e.injective
      rw [ContinuousMulEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · show 1 = infiniteEquiv E N ((prodEquiv E N) ((prodEquiv E N).symm (1, _))).1
        simp
      · show b = finiteRestrictedEquiv E N ((prodEquiv E N) ((prodEquiv E N).symm (1, _))).2
        simp
    rw [hΔ, he]
    exact modularCharacter_eq_one_of_compact μ _ hcomp (Subgroup.mem_map_of_mem _ hk)
  have hall : ∀ z, Δ z = 1 := fun z => by
    have hz : z = (z.1, 1) * (1, z.2) := by simp
    rw [hz, map_mul]
    have a1 : Δ (z.1, 1) = 1 :=
      pi_eq_one (Δ.comp (MonoidHom.inl (PInf E N) (PFin E N))) (fun w x => hinf w x) z.1
    have a2 : Δ (1, z.2) = 1 :=
      restricted_eq_one (Δ.comp (MonoidHom.inr (PInf E N) (PFin E N))) (fun v x => hfin v x) (fun b hb => hint b hb) z.2
    rw [a1, a2, one_mul]
  have := hall (e g)
  rwa [hΔ, ContinuousMulEquiv.symm_apply_apply] at this

end Adelic

theorem isMulRightInvariant_GA_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant :=
  fun E _ _ _ N μ _ => isMulRightInvariant_GA E N μ

end GlobalTheory.CompanionTheory.AdelicUnimod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqL2Inner
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem setIntegral_mul_conj_eq_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ → ∀ x y : Sm E N, x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → ∫ g in F, x.1 g * (starRingEnd ℂ) (y.1 g) ∂μ = ⟪l2Map μ y, l2Map μ x⟫_ℂ := by
  intro E _ _ _ N μ _ F hF x y hx hy
  rw [l2Map_apply μ hx, l2Map_apply μ hy, MemL2Quotient.inner_toL2_eq_theta_pairing, pet_eq hF ((mem_l2Sub μ).1 hx).1 ((mem_l2Sub μ).1 hy).1]

end GlobalTheory.CompanionTheory.FinDiscOrth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNormalisedOfDualIsConj
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F
open GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.OneExDatum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev sConj (x : HeightOneSpectrum (𝓞 E)) :
    GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E) →* GL (Fin n) (x.adicCompletion E) :=
  GeneralLinearGroup.map (n := Fin n) (conjLoc (IsCMField.complexConj E).toRingEquiv x)

theorem exists_equiv_of_dualIsConj {π : CuspSub E n} (hd : GlobalTheory.ContraPair.DualIsConj π) (x : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E)))
    (τ : SmIrr (GL (Fin n) (x.adicCompletion E))) (hσ : π.IsLocComp (GlobalTheory.ThetaSatake.cw x) σ)
    (ha : IsAdmissible σ.ρ) (hτ : π.IsLocComp x τ) :
    ∃ T : σ.V ≃ₗ[ℂ] τ.V, ∀ g v, τ.ρ (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc x) n g) (T v) = T (σ.ρ g v) := by
  obtain ⟨B, -, hB, hfinB, -, -⟩ := hd
  obtain ⟨f, f0, hf⟩ := hτ
  have hs : Continuous (sConj (n := n) x) :=
    Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ x).1)
  let τ' : SmIrr (GL (Fin n) ((GlobalTheory.ThetaSatake.cw x).adicCompletion E)) :=
    { V := τ.V, ρ := MonoidHom.comp τ.ρ (sConj x), smooth := fun v => (τ.smooth v).preimage hs
      irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (GlobalTheory.ConjPairLoc.map_conjLoc_surjective x) τ.irred }
  have hσ' := ((cuspSub_iff π).2.1 _ σ).2 hσ
  let β : π.V →ₗ[ℂ] τ.V →ₗ[ℂ] ℂ := B.compl₂ f
  have hβ : β ≠ 0 := fun h => f0 (LinearMap.ext fun v =>
    hB (f v) fun φ => LinearMap.congr_fun (LinearMap.congr_fun h φ) v)
  obtain ⟨F, hF⟩ := GlobalTheory.LocDual.exists_comp_ne_zero π.V π.stable π.irred _ σ hσ' β hβ
  let P : σ.V →ₗ[ℂ] τ.V →ₗ[ℂ] ℂ := β ∘ₗ F.1.codRestrict π.V F.2.1
  have hP : ∀ g u v, P (σ.ρ g u) (τ'.ρ g v) = P u v := fun g u v => by
    have e1 : F.1.codRestrict π.V F.2.1 (σ.ρ g u) =
        π.op (.fin (locGL E n _ g)) (F.1.codRestrict π.V F.2.1 u) := Subtype.ext (F.2.2 g u)
    have e2 : f (τ'.ρ g v) = π.op (GlobalTheory.ContraPair.conjOp (.fin (locGL E n _ g))) (f v) := by
      change f (τ.ρ (sConj x g) v) = π.op (.fin (GeneralLinearGroup.map _ (locGL E n _ g))) (f v)
      rw [GlobalTheory.ConjPairLoc.conjFin_locGL, hf, CuspSub.locRep_eq]
    change B (F.1.codRestrict π.V F.2.1 (σ.ρ g u)) (f (τ'.ρ g v)) = B (F.1.codRestrict π.V F.2.1 u) (f v)
    rw [e1, e2, hfinB]
  have hirr : (GlobalTheory.SmGL.contra σ.ρ).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis _ n) ha σ.irred
  let e₁ := (GlobalTheory.InvPairing.pairMap σ.ρ τ'.smooth P hP).ofBijective
    (GlobalTheory.InvPairing.pairMap_bijective σ.ρ τ'.smooth P hP hF τ'.irred hirr)
  obtain ⟨e₂⟩ := GlobalTheory.GelfandKazhdan.equiv_contra _ n σ.V σ.ρ ha σ.irred
  let e : σ.V ≃ₗ[ℂ] τ.V := (e₂.trans e₁.symm).toLinearEquiv
  have he : ∀ g v, e (σ.ρ g v) = τ.ρ (sConj x (invT n _ g)) (e v) := fun g v => by
    have h := GlobalTheory.ConjPairLoc.equiv_apply (e₂.trans e₁.symm) (invT n _ g) v
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose n _ (invT n _ g) = g := Units.ext (Matrix.transpose_transpose _)
    rw [MonoidHom.comp_apply, h1] at h
    exact h
  refine ⟨e, fun g v => ?_⟩
  rw [he]
  congr 2
  exact Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

theorem eq_cw_of_conjPl {w u : HeightOneSpectrum (𝓞 E)} (h : ConjPl w u) : u = GlobalTheory.ThetaSatake.cw w := by
  obtain ⟨h1, h2⟩ := h
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w).1 h1.symm with e | e
  · subst e
    rcases h2 with h2 | h2
    · exact absurd rfl h2
    · exact (GlobalTheory.BCT.LocMem.conjSrc_eq_of_not_split _ h2).symm
  · exact eq_conjSrc e

end GlobalTheory.CompanionTheory.OneExDatum

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointBis
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem lie_skew_l2Map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : Lie E N) (x y : Sm E N), Continuous x.1 → Continuous y.1 → Continuous (lie E N X x).1 → Continuous (lie E N X y).1 → x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X x ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X y ∈ squareIntegrableSmoothSubmoduleGL μ → ⟪l2Map μ x, l2Map μ (lie E N X y)⟫_ℂ = -⟪l2Map μ (lie E N X x), l2Map μ y⟫_ℂ := by
  intro E _ _ _ N μ _ _ X x y cx cy cXx cXy hx hy hXx hXy
  rw [l2Map_apply μ hx, l2Map_apply μ hy, l2Map_apply μ hXx, l2Map_apply μ hXy,
    GlobalTheory.CompanionTheory.LieSkew.lie_skew E N μ X x y ((mem_l2Sub μ).1 hx) ((mem_l2Sub μ).1 hy)
      ((mem_l2Sub μ).1 hXx) ((mem_l2Sub μ).1 hXy) cx cy cXx cXy, neg_neg]

end GlobalTheory.CompanionTheory.FinDiscOrth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarScalingByUnitStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_haar_scaling_by_unit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), lam.IsAddHaarMeasure → ∀ n : (Fv F v)ˣ, lam.map (fun t => (n : Fv F v) * t) = (‖(n : Fv F v)‖₊)⁻¹ • lam := by
  first | exact @GlobalTheory.CompanionTheory.Haar.map_mul_left | exact GlobalTheory.CompanionTheory.Haar.map_mul_left | (intros; apply GlobalTheory.CompanionTheory.Haar.map_mul_left <;> assumption)
end

