module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteClassSetHermitianUnitaryOpenLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct Pointwise

namespace GlobalTheory.Mem.VolFin

theorem measure_lt_top_of_cover {G A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [LocallyCompactSpace B] [SecondCountableTopology B]
    [MeasurableSpace B] [BorelSpace B]
    (e : G ≃ₜ* A × B) (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure]
    (S : Finset B) (K : Set B) (hK : IsCompact K) (Ω : B → Set A)
    (hΩ : ∀ s, (Measure.haar : Measure A) (Ω s) < ⊤)
    (hcov : ∀ g : G, ∃ γ : Γ, ∃ s ∈ S, (e (γ • g)).1 ∈ Ω s ∧ (e (γ • g)).2 ∈ s • K)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : μ 𝓕 < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have h1 : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  have h2 := Measure.isMulLeftInvariant_eq_smul (μ.map e)
    ((Measure.haar : Measure A).prod (Measure.haar : Measure B))
  have hle : μ 𝓕 ≤ μ (⋃ s ∈ S, e ⁻¹' (Ω s ×ˢ (s • K))) := by
    refine GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers h𝓕 (.of_forall fun g => ?_)
    obtain ⟨γ, s, hs, h⟩ := hcov g
    exact ⟨γ, Set.mem_biUnion hs h⟩
  refine hle.trans_lt ((measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.2 fun s _ => ?_))
  refine (Measure.le_map_apply (map_continuous e).measurable.aemeasurable _).trans_lt ?_
  rw [h2, Measure.smul_apply, Measure.prod_prod]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top (hΩ s) (hK.smul s).measure_lt_top)

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (x : E) :
    sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := by
  simp [sigR, inclR]

noncomputable def ratPt (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Formalism.UG.UJ (σ : E →+* E) J →* HA R σ J where
  toFun γ := (⟨Formalism.UG.bc (inclR (F := F) R) γ.1, by
    have := congrArg (fun N => N.map (inclR (F := F) R)) (show Formalism.UG.cT _ _ * _ * _ = _ from γ.2)
    simp only [Matrix.map_mul] at this
    change Formalism.UG.cT _ _ * _ * _ = _
    refine Eq.trans ?_ this
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ rfl) rfl
    ext i j
    exact sigR_inclR R σ _⟩ : HR R σ J)
  map_one' := Subtype.ext (map_one (Formalism.UG.bc (inclR (F := F) R)))
  map_mul' a b := Subtype.ext (map_mul (Formalism.UG.bc (inclR (F := F) R)) _ _)

theorem topGroup_HA [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem countable_HFinIn [Countable E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Countable (HFinIn R σ J) := by
  haveI : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  haveI : Countable (GL (Fin M) E) := Units.val_injective.countable
  refine Function.Surjective.countable
    (f := fun γ : Formalism.UG.UJ (σ : E →+* E) J => (⟨ratPt R σ J γ, γ.1, γ.2, rfl⟩ : HFinIn R σ J)) ?_
  rintro ⟨g, γ, hγ, h⟩
  exact ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext h)⟩

variable [NumberField F]

theorem mulVec_fv {M : ℕ} (m : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    (m.map (inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))).mulVec (GlobalTheory.AdLat.fv F x) = GlobalTheory.AdLat.fv F (m.mulVec x) := by
  ext i
  exact (RingHom.map_mulVec (inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) m x i).symm

theorem mulVec_mem_hat_of_rat {M : ℕ} (m : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (h : ∀ x ∈ Λ, m.mulVec x ∈ Λ) {z : Fin M → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E} (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E))) :
    (m.map (inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))).mulVec z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) := by
  refine GlobalTheory.AdLat.Translate.mulVec_mem_hat (fun x hx => ?_) hz
  rw [SetLike.mem_coe, GlobalTheory.AdLat.Translate.mem_pre, mulVec_fv]
  exact GlobalTheory.AdLat.Translate.fv_mem_hat (h x hx)

theorem stabHat_conj {M : ℕ} (δ : GL (Fin M) E) (L Λ : Submodule (𝓞 E) (Fin M → E))
    (s : GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))
    (hΛ : (GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) : Set (Fin M → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) =
      (s : Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)).mulVec '' (GlobalTheory.AdLat.hat F (L : Set (Fin M → E))))
    (h : ∀ x, x ∈ Λ ↔ (δ : Matrix (Fin M) (Fin M) E).mulVec x ∈ Λ) :
    StabHat F (L : Set (Fin M → E))
      ((s⁻¹ * Formalism.UG.bc (inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) δ * s : GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) :
        Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) := by
  have him : ∀ y, y ∈ latHat F E (L : Set (Fin M → E)) ↔
      (s : Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)).mulVec y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E)) := by
    intro y
    rw [← SetLike.mem_coe (p := GlobalTheory.AdLat.hat F (Λ : Set (Fin M → E))), hΛ]
    constructor
    · exact fun hy => ⟨y, hy, rfl⟩
    · rintro ⟨u, hu, huy⟩
      have := congrArg ((s⁻¹ : GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)).mulVec huy
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.one_mulVec] at this
      exact this ▸ hu
  intro y
  rw [him, him, Matrix.mulVec_mulVec y, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
    Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨mulVec_mem_hat_of_rat _ Λ fun x hx => (h x).1 hx, fun hz => ?_⟩
  have := mulVec_mem_hat_of_rat ((δ⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Λ (fun x hx => by
    rw [h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hx) hz
  change ((Formalism.UG.bc (inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) δ⁻¹ : GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)).mulVec _ ∈ _ at this
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at this

end Rat

theorem finVol : FiniteVolume₂ := by
  intro F E _ _ _ _ _ σ hCM M J hJ μ hμ 𝓕 h𝓕
  classical
  haveI := topGroup_HA (AF F) σ J
  haveI := topGroup_HA (Ainf F) σ J
  haveI := topGroup_HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Ainf F) σ J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
  obtain ⟨_, _, -⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Ainf F) σ M J
  obtain ⟨_, _, -⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ M J
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  haveI : Countable Γ := countable_HFinIn (AF F) σ J
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E σ M J
  have herat : ∀ γ, e (ratPt (AF F) σ J γ) = (ratPt (Ainf F) σ J γ, ratPt (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J γ) := by
    intro γ
    refine Prod.ext (Subtype.ext (Units.ext ((he _).2.trans ?_))) (Subtype.ext (Units.ext ((he _).1.trans ?_)))
    · ext i j
      change Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (inclR (F := F) (AF F) _) = inclR (F := F) (Ainf F) _
      simp [inclR]
    · ext i j
      change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (inclR (F := F) (AF F) _) = inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
      simp [inclR]
  let b := Pi.basisFun E (Fin M)
  let L : Submodule (𝓞 E) (Fin M → E) := Submodule.span (𝓞 E) (Set.range b)
  have hL : L.FG := Submodule.fg_span (Set.finite_range b)
  have hLs : Submodule.span E (L : Set (Fin M → E)) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨K, hK, hKo, hKc⟩ := _root_.GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab F E σ M J L hL hLs
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.Mem.ClassFinite.exists_finset_classes F E σ hCM M J hJ K hKo
  choose Λ _ hΛ1 hΛ2 hΛ3 using fun s : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J =>
    GlobalTheory.AdLat.exists_lattice_latOf F E M L (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J s) hL hLs
  choose Ω _ hΩ1 hΩ2 using fun s : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J =>
    GlobalTheory.T.finite_covolume_latticeStabiliser_unitaryRealPoints F E σ hCM M J hJ (Λ s) (hΛ1 s) (hΛ2 s) Measure.haar inferInstance
  refine measure_lt_top_of_cover e Γ μ S K hKc Ω hΩ1 (fun g => ?_) 𝓕 h𝓕
  obtain ⟨⟨γ', γ, hγ, hγγ⟩, s, hs, k, hk, hg⟩ := hS (e g).2
  have hg2 : (e g).2 = ratPt (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J ⟨γ, hγ⟩ * (s * k) := by
    rw [hg]
    exact congrArg (· * (s * k)) (Subtype.ext hγγ.symm : (γ' : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J) = ratPt (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J ⟨γ, hγ⟩)
  obtain ⟨δ, hδ, hδΛ, w, hw, hwe⟩ := hΩ2 s ((ratPt (Ainf F) σ J ⟨γ, hγ⟩)⁻¹ * (e g).1)
  have hw1 : (ratPt (Ainf F) σ J ⟨γ, hγ⟩)⁻¹ * (e g).1 = ratPt (Ainf F) σ J ⟨δ, hδ⟩ * w := Subtype.ext hwe
  have hkδ : s⁻¹ * ratPt (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J ⟨δ, hδ⟩ * s ∈ K :=
    (hK _).2 (stabHat_conj δ L (Λ s) (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J s) (hΛ3 s) hδΛ)
  let η : Formalism.UG.UJ (σ : E →+* E) J := (⟨δ, hδ⟩ : Formalism.UG.UJ (σ : E →+* E) J)⁻¹ * (⟨γ, hγ⟩ : Formalism.UG.UJ (σ : E →+* E) J)⁻¹
  refine ⟨⟨ratPt (AF F) σ J η, η.1, η.2, rfl⟩, s, hs, ?_, ?_⟩
  · change (e (ratPt (AF F) σ J η * g)).1 ∈ _
    rw [map_mul, herat, Prod.fst_mul, map_mul, map_inv, map_inv, mul_assoc, hw1, inv_mul_cancel_left]
    exact hw
  · change (e (ratPt (AF F) σ J η * g)).2 ∈ _
    rw [map_mul, herat, Prod.snd_mul]
    dsimp only
    rw [map_mul, map_inv, map_inv, mul_assoc, hg2, inv_mul_cancel_left]
    refine ⟨_, K.mul_mem (K.inv_mem hkδ) hk, ?_⟩
    simp only [smul_eq_mul]
    group

end GlobalTheory.Mem.VolFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Datum Matrix
open scoped InnerProductSpace Classical

namespace GlobalTheory.JointHarm

section Hol

variable {n : ℕ} {P : Type} [AddCommGroup P] [Module ℂ P]

def IsHolRep (ε : Fin n → Bool) (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) : Prop :=
  (∀ x, B x x = 0 → x = 0) ∧ π 1 = 1 ∧
    (∀ a ∈ GlobalTheory.Dec.KC ε, ∀ b ∈ GlobalTheory.Dec.KC ε, π (a * b) = π a * π b) ∧
    (∀ g ∈ GlobalTheory.Dec.KC ε, ∀ x y, B (π g x) y = B x (π gᴴ y)) ∧
    ∀ x y, DifferentiableOn ℂ (fun g : Fin n → Fin n → ℂ => B x (π (Matrix.of g) y))
      {g | Matrix.of g ∈ GlobalTheory.Dec.KC ε}

def IsBottom (ε : Fin n → Bool) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (μ : Fin n → ℝ) (x : P) : Prop :=
  (∀ g ∈ GlobalTheory.Dec.KC ε, IsLoUni g → π g x = x) ∧
    ∀ θ : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) x =
      Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • x

variable {ι : Type}

def IsHolFam (ε : ι → Fin n → Bool) (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
    (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) : Prop :=
  (∀ x, B x x = 0 → x = 0) ∧ ϖ 1 = 1 ∧
    (∀ a b, (∀ τ, a τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, b τ ∈ GlobalTheory.Dec.KC (ε τ)) → ϖ (a * b) = ϖ a * ϖ b) ∧
    ∀ τ, IsHolRep (ε τ) B fun g => ϖ (Pi.mulSingle τ g)

def IsBotFam (ε : ι → Fin n → Bool) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P)
    (μ : ι → Fin n → ℝ) (x : P) : Prop :=
  ∀ τ, IsBottom (ε τ) (fun g => ϖ (Pi.mulSingle τ g)) (μ τ) x

theorem isHolRep_of_isTau {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : GlobalTheory.Dec.IsTau ε abelian₂ τ w) :
    IsHolRep ε (innerₛₗ ℂ) (fun g => (τ g : W →ₗ[ℂ] W)) ∧
      IsBottom ε (fun g => (τ g : W →ₗ[ℂ] W)) (-abelian₂) w := by
  obtain ⟨-, ⟨h1, hm⟩, hd, ha, -, -, hw, hl⟩ := h
  refine ⟨⟨fun x hx => inner_self_eq_zero.1 hx, ?_, fun a ha b hb => ?_, ha, hd⟩, hl, fun θ => hw θ ⟨?_, ?_⟩⟩
  · show (τ 1 : W →ₗ[ℂ] W) = 1
    rw [h1]; rfl
  · show (τ (a * b) : W →ₗ[ℂ] W) = _
    rw [hm a ha b hb]; rfl
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [← Complex.exp_conj, ← Complex.exp_add]
  · simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

end Hol

section Fock

variable {D : D7} {m n : ℕ}

def fsub (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : PolF D m n →ₐ[ℂ] PolF D m n :=
  MvPolynomial.aeval fun v => ∑ a : Fin m, ∑ b : Fin n,
    MvPolynomial.C (if ε v.1 v.2.1 = true then k v.1 a v.2.1 * (u v.1)⁻¹ v.2.2 b
      else (k v.1)⁻¹ v.2.1 a * u v.1 b v.2.2) * MvPolynomial.X (v.1, a, b)

def detP (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) * k + (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε)).det

def detM (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) * k + (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε)).det

def fchar (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ τ, detP (ε τ) (k τ) ^ x₁ τ * detM (ε τ) (k τ) ^ x₂ τ * (u τ).det ^ x₃ τ

def fact (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (PolF D m n) :=
  fchar ε x₁ x₂ x₃ k u • (fsub ε k u).toLinearMap

def factK (n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (g : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : Module.End ℂ (PolF D m n) :=
  fact ε x₁ x₂ x₃ (fun τ => ((g τ)⁻¹)ᵀ) 1

def factU (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (PolF D m n) :=
  fact ε x₁ x₂ x₃ 1 u

def wtK (p : ℕ) (ap am : ℕ → ℕ) (x₁ x₂ : ℤ) (a : Fin m) : ℤ :=
  if (a : ℕ) < p then (ap a : ℤ) + x₁ else -(am (m - 1 - a) : ℤ) + x₂

def wtU (p q : ℕ) (ap am : ℕ → ℕ) (x₃ : ℤ) (j : Fin n) : ℤ :=
  -(if (j : ℕ) < p then (ap j : ℤ) else 0) + (if n - 1 - j < q then (am (n - 1 - j) : ℤ) else 0) + x₃

end Fock

def vact {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (u : ι → Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (Pol ℂ ι n) :=
  (∏ τ, (u τ).det ^ (-(lam τ).detShift)) • (Formalism.GradedWeylDivisibility.blockAct ℂ fun τ => (u τ)⁻¹).toLinearMap

end GlobalTheory.JointHarm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecTheta

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem isThetaFunO_of_thetaAt (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {e : AE D} {Λ : AddSubgroup (WO S T)}
    {c : ℂ} {f₀ Φ f : WO S T → ℂ} (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h₀ : IsThetaFunO ψ S T f₀) : IsThetaFunO ψ S T f := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  show f ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    LinearMap.pi fun w => l ∘ₗ GlobalTheory.SplitScalar.heisL ψ S T w
  have hA0 : ∀ g w, A g w = l (heisO ψ S T w g) := fun _ _ => rfl
  have hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g) := fun u g => by
    funext w
    rw [hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]
    rfl
  have hf0 : A f₀ = 0 := by
    funext w
    exact (Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.trans Φ hΦ x hx, hA x]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T x).map_add _ _).symm
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.modul Φ hΦ y hy, hA y]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T y).map_add _ _).symm
      vac := by
        rw [LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hall _ hT'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  have e3 := congrFun (left_eq_add.1 e2) 0
  rwa [hA0, GlobalTheory.OrientedHeis.heisO_zero] at e3

variable {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
  {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
  {ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ}

theorem isThetaFunO_stepVec {LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank}
    {χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) : IsThetaFunO ψ S T f := by
  obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := h
  exact isThetaFunO_of_thetaAt hψ h0.inf h h0.theta

theorem isThetaFunO_thPVec {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) : IsThetaFunO ψ S T f := by
  obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := h
  exact isThetaFunO_of_thetaAt hψ h0.inf h h0.theta

end GlobalTheory.VecTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenNormCoeffOfFibreStatement
section
open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_basicOpen_normCoeff_of_fibre : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f] {V : X.Opens} (hV : IsAffineOpen V)
    [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)] (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X), x ∈ V →
    (∀ y : Y, f y = x → y ∈ Y.basicOpen τ) →
    ∃ k, 1 ≤ k ∧ x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := by
  first | exact @GlobalTheory.NormalDescent.mem_basicOpen_normCoeff_of_fibre | exact GlobalTheory.NormalDescent.mem_basicOpen_normCoeff_of_fibre | (intros; apply GlobalTheory.NormalDescent.mem_basicOpen_normCoeff_of_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeterssonNormSqPosAutomorphicFunctionUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.PetPos

theorem sq_integral_pos {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] (𝓕 : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (φ : G → ℂ) (hl : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (hc : Continuous φ) (h0 : φ ≠ 0)
    (hi : IntegrableOn (fun h => star (φ h) * φ h) 𝓕 μ) : 0 < (∫ h in 𝓕, star (φ h) * φ h ∂μ).re := by
  have hre : ∀ h, (star (φ h) * φ h).re = Complex.normSq (φ h) := fun h => by
    simp [Complex.normSq_apply]
  have e1 : (∫ h in 𝓕, star (φ h) * φ h ∂μ).re = ∫ h in 𝓕, Complex.normSq (φ h) ∂μ := by
    have := integral_re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, hre] at this
    exact this.symm
  have hi' : IntegrableOn (fun h => Complex.normSq (φ h)) 𝓕 μ := by
    have := Integrable.re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, hre] at this
    exact this
  rw [e1, setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun h => Complex.normSq_nonneg _) hi']
  have hs : Function.support (fun h => Complex.normSq (φ h)) = Function.support φ := by
    ext h
    simp [Function.mem_support]
  rw [hs, pos_iff_ne_zero]
  intro hz
  have hinv : ∀ γ : Γ, γ • Function.support φ = Function.support φ := fun γ => by
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
    have : φ (γ⁻¹ • g) = φ g := hl _ (γ⁻¹).2 g
    rw [this]
  have hzero := h𝓕.measure_zero_of_invariant _ hinv hz
  exact (hc.isOpen_support.measure_pos μ (Function.support_nonempty_iff.2 h0)).ne' hzero

theorem petersson_pos : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsQuot V μ 𝓕 → ∀ φ, IsAutFun V φ → φ ≠ 0 → IntegrableOn (fun h => star (φ h) * φ h) 𝓕 μ → 0 < (∫ h in 𝓕, star (φ h) * φ h ∂μ).re := by
  intro D V μ 𝓕 hq φ hφ h0 hi
  obtain ⟨-, -, -, h4, h5, -, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hH := hq.1
  exact sq_integral_pos (GQ V) μ 𝓕 hq.2 φ hφ.left hφ.cont h0 hi

end GlobalTheory.Mem.PetPos
end

