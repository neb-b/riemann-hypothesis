module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGenB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabilizerConjFiniteAdeleGLIntegral
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.StabLat

variable {F : Type} [Field F] [NumberField F]

def IntV {n : ℕ} (x : Fin n → FiniteAdeleRing (𝓞 F) F) : Prop := ∀ i, x i ∈ PIW.ClassFinD.Ohat F

def emb {n : ℕ} (y : Fin n → F) : Fin n → FiniteAdeleRing (𝓞 F) F := fun i => algebraMap F _ (y i)

theorem intV_add {n : ℕ} {x y : Fin n → FiniteAdeleRing (𝓞 F) F} (hx : IntV x) (hy : IntV y) : IntV (x + y) :=
  fun i => (PIW.ClassFinD.Ohat F).add_mem (hx i) (hy i)

theorem intV_sub {n : ℕ} {x y : Fin n → FiniteAdeleRing (𝓞 F) F} (hx : IntV x) (hy : IntV y) : IntV (x - y) :=
  fun i => (PIW.ClassFinD.Ohat F).sub_mem (hx i) (hy i)

theorem intV_smul {n : ℕ} {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ PIW.ClassFinD.Ohat F)
    {x : Fin n → FiniteAdeleRing (𝓞 F) F} (hx : IntV x) : IntV (a • x) :=
  fun i => (PIW.ClassFinD.Ohat F).mul_mem ha (hx i)

theorem intV_mulVec {n : ℕ} {A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)}
    (hA : ∀ i j, A i j ∈ PIW.ClassFinD.Ohat F) {z : Fin n → FiniteAdeleRing (𝓞 F) F} (hz : IntV z) :
    IntV (A *ᵥ z) := fun i => by
  show ∑ j, A i j * z j ∈ _
  exact (PIW.ClassFinD.Ohat F).sum_mem fun j _ => (PIW.ClassFinD.Ohat F).mul_mem (hA i j) (hz j)

theorem intV_single {n : ℕ} (j : Fin n) : IntV (Pi.single j (1 : FiniteAdeleRing (𝓞 F) F)) := fun i => by
  by_cases h : i = j
  · subst h; rw [Pi.single_eq_same]; exact (PIW.ClassFinD.Ohat F).one_mem
  · rw [Pi.single_eq_of_ne h]; exact (PIW.ClassFinD.Ohat F).zero_mem

theorem int_mem (c : 𝓞 F) : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F c) ∈ PIW.ClassFinD.Ohat F :=
  fun v => by
    show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Formalism.MainNotions.BridgeLevelGenB.val_int]
    exact HeightOneSpectrum.intValuation_le_one v c

theorem exists_int_of_mem (f : F) (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ PIW.ClassFinD.Ohat F) :
    f ∈ (algebraMap (𝓞 F) F).range :=
  HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F f fun v => by
    have hv : algebraMap F (v.adicCompletion F) f ∈ v.adicCompletionIntegers F := h v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers, PI.WAU.val_algebraMap_F] at hv

theorem exists_den (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ N : ℕ, 0 < N ∧ (N : FiniteAdeleRing (𝓞 F) F) * a ∈ PIW.ClassFinD.Ohat F :=
  PI.WAU.B.exists_nat_adele a

theorem exists_den_mat {n : ℕ} (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ i j, (N : FiniteAdeleRing (𝓞 F) F) * A i j ∈ PIW.ClassFinD.Ohat F := by
  classical
  choose m hm h using fun q : Fin n × Fin n => exists_den (A q.1 q.2)
  refine ⟨∏ q, m q, Finset.prod_pos fun q _ => hm q, fun i j => ?_⟩
  obtain ⟨k, hk⟩ : m (i, j) ∣ ∏ q, m q := Finset.dvd_prod_of_mem m (Finset.mem_univ _)
  rw [hk, Nat.cast_mul, mul_comm ((m (i, j) : ℕ) : FiniteAdeleRing (𝓞 F) F), mul_assoc]
  exact (PIW.ClassFinD.Ohat F).mul_mem (natCast_mem (PIW.ClassFinD.Ohat F) k) (h (i, j))

theorem exists_approx (a : FiniteAdeleRing (𝓞 F) F) (M : ℕ) (hM : 0 < M) :
    ∃ f : F, ∃ c ∈ PIW.ClassFinD.Ohat F, a = algebraMap F _ f + (M : FiniteAdeleRing (𝓞 F) F) * c := by
  obtain ⟨N, hN, hNa⟩ := exists_den a
  obtain ⟨s, c, hc, hs⟩ := Formalism.MainNotions.BridgeLevelGenB.dense_mod (N * M) (Nat.mul_pos hN hM) _ (fun v => hNa v)
  refine ⟨algebraMap (𝓞 F) F s * (N : F)⁻¹, c, fun v => hc v, ?_⟩
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hinv : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((N : F)⁻¹) * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul, inv_mul_cancel₀ hN0, map_one]
  calc a = algebraMap F _ ((N : F)⁻¹) * ((N : FiniteAdeleRing (𝓞 F) F) * a) := by rw [← mul_assoc, hinv, one_mul]
    _ = _ := by
      rw [hs, map_mul, Nat.cast_mul]
      linear_combination ((M : FiniteAdeleRing (𝓞 F) F) * c) * hinv

theorem exists_approx_vec {n : ℕ} (x : Fin n → FiniteAdeleRing (𝓞 F) F) (M : ℕ) (hM : 0 < M) :
    ∃ f : Fin n → F, ∃ c : Fin n → FiniteAdeleRing (𝓞 F) F, IntV c ∧
      x = emb f + (M : FiniteAdeleRing (𝓞 F) F) • c := by
  choose f c hc h using fun i => exists_approx (x i) M hM
  exact ⟨f, c, hc, funext fun i => by simpa [emb, smul_eq_mul] using h i⟩

theorem emb_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (y : Fin n → F) :
    (A.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) *ᵥ emb y = emb (A *ᵥ y) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap F (FiniteAdeleRing (𝓞 F) F)) A y i).symm


variable (F) in
def lat {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Submodule (𝓞 F) (Fin n → F) where
  carrier := {y | IntV (((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ emb y)}
  add_mem' := by
    intro x y hx hy
    have e : emb (x + y) = emb x + (emb y : Fin n → FiniteAdeleRing (𝓞 F) F) := by
      ext i; simp [emb]
    show IntV _
    rw [e, mulVec_add]
    exact intV_add hx hy
  zero_mem' := by
    show IntV _
    have e : emb (0 : Fin n → F) = (0 : Fin n → FiniteAdeleRing (𝓞 F) F) := by ext i; simp [emb]
    rw [e, mulVec_zero]
    exact fun i => (PIW.ClassFinD.Ohat F).zero_mem
  smul_mem' := by
    intro c y hy
    have e : emb (c • y) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F c) • emb y := by
      ext i; simp [emb, Algebra.smul_def]
    show IntV _
    rw [e, mulVec_smul]
    exact intV_smul (int_mem c) hy

theorem mem_lat {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) (y : Fin n → F) :
    y ∈ lat F s ↔ IntV (((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ emb y) := Iff.rfl

end GlobalTheory.StabLat

namespace GlobalTheory.StabLat

variable {F : Type} [Field F] [NumberField F]

theorem lat_fg {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : (lat F s).FG := by
  obtain ⟨D, hD, hDS⟩ := exists_den_mat ((s : GL (Fin n) _) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))
  have hD0 : ((D : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast hD.ne'
  refine Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.fg_of_le_bnd hD0 fun y hy => ?_
  rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.mem_bnd]
  intro a
  apply exists_int_of_mem
  have hI : IntV ((D : FiniteAdeleRing (𝓞 F) F) • emb y) := by
    have e : (D : FiniteAdeleRing (𝓞 F) F) • emb y =
        ((D : FiniteAdeleRing (𝓞 F) F) • ((s : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) *ᵥ
          ((((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) *ᵥ emb y) := by
      rw [Matrix.mulVec_mulVec, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [e]
    exact intV_mulVec (fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hDS i j) hy
  have := hI a
  simpa [emb, map_natCast] using this

theorem lat_span {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    Submodule.span F (lat F s : Set (Fin n → F)) = ⊤ := by
  obtain ⟨D, hD, hDS⟩ := exists_den_mat (((s⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)))
  have hD0 : (D : F) ≠ 0 := by exact_mod_cast hD.ne'
  have hmem : ∀ j : Fin n, (D : F) • Pi.single j (1 : F) ∈ lat F s := by
    intro j
    rw [mem_lat]
    have e : emb ((D : F) • Pi.single j (1 : F)) =
        (D : FiniteAdeleRing (𝓞 F) F) • (Pi.single j 1 : Fin n → FiniteAdeleRing (𝓞 F) F) := by
      funext i
      by_cases h : i = j
      · subst h; simp [emb]
      · simp [emb, Pi.single_eq_of_ne h]
    rw [e, Matrix.mulVec_smul]
    intro i
    rw [Pi.smul_apply, Matrix.mulVec_single_one, smul_eq_mul]
    exact hDS i j
  rw [eq_top_iff, ← (Pi.basisFun F (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [Pi.basisFun_apply]
  have h1 : Pi.single j (1 : F) = (D : F)⁻¹ • ((D : F) • Pi.single j (1 : F)) := by
    rw [smul_smul, inv_mul_cancel₀ hD0, one_smul]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem j))

theorem lat_isLattice {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    Submodule.IsFullLattice F (lat F s) := by
  exact { toIsLattice := Submodule.IsLattice.of_fg F (lat_fg s), span_eq_top := lat_span s }

theorem matInt_conj {n : ℕ} (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) F)
    (h : ∀ y ∈ lat F s, (γ : Matrix (Fin n) (Fin n) F) *ᵥ y ∈ lat F s) :
    PIW.ClassFinD.MatInt ((s⁻¹ * PIW.ClassFinD.glIncl F n γ * s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) := by
  set S : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) := s.val with hS
  set Si : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) := (s⁻¹).val with hSi
  set G : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
    (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) with hG
  have hA : ((s⁻¹ * PIW.ClassFinD.glIncl F n γ * s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) = Si * G * S := by
    rw [Units.val_mul, Units.val_mul]; rfl
  have hSiS : Si * S = 1 := by rw [hSi, hS, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSSi : S * Si = 1 := by rw [hSi, hS, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hA]
  obtain ⟨N, hN, hNA⟩ := exists_den_mat (Si * G * S)
  obtain ⟨D, hD, hDSi⟩ := exists_den_mat Si
  suffices key : ∀ z, IntV z → IntV ((Si * G * S) *ᵥ z) by
    intro i j
    have := key (Pi.single j (1 : FiniteAdeleRing (𝓞 F) F)) (intV_single j) i
    rw [Matrix.mulVec_single_one] at this
    exact this
  intro z hz
  obtain ⟨f, c, hc, hSz⟩ := exists_approx_vec (S *ᵥ z) (N * D) (Nat.mul_pos hN hD)
  set u : Fin n → FiniteAdeleRing (𝓞 F) F := (D : FiniteAdeleRing (𝓞 F) F) • (Si *ᵥ c) with hu
  have hui : IntV u := by
    rw [hu, ← Matrix.smul_mulVec]
    exact intV_mulVec (fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hDSi i j) hc
  have hz' : Si *ᵥ emb f = z - (N : FiniteAdeleRing (𝓞 F) F) • u := by
    have e : emb f = S *ᵥ z - ((N * D : ℕ) : FiniteAdeleRing (𝓞 F) F) • c := eq_sub_of_add_eq hSz.symm
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hSiS, Matrix.one_mulVec, Matrix.mulVec_smul, hu,
      Nat.cast_mul, mul_smul]
  have hf : f ∈ lat F s := by
    rw [mem_lat]
    change IntV (Si *ᵥ emb f)
    rw [hz']
    exact intV_sub hz (intV_smul (natCast_mem _ N) hui)
  have hγf := h f hf
  rw [mem_lat, ← emb_mulVec, Matrix.mulVec_mulVec] at hγf
  have hzE : z = Si *ᵥ emb f + (N : FiniteAdeleRing (𝓞 F) F) • u := by rw [hz', sub_add_cancel]
  have e2 : (Si * G * S) *ᵥ z = (Si * G) *ᵥ emb f + ((N : FiniteAdeleRing (𝓞 F) F) • (Si * G * S)) *ᵥ u := by
    rw [hzE, Matrix.mulVec_add, Matrix.mulVec_mulVec, mul_assoc (Si * G), hSSi, mul_one, Matrix.mulVec_smul,
      Matrix.smul_mulVec]
  rw [e2]
  exact intV_add hγf (intV_mulVec (fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hNA i j) hui)

end GlobalTheory.StabLat


open GlobalTheory.StabLat in
theorem GlobalTheory.StabLat.exists_lattice_stab_conj :
    ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
      ∃ Λ : Submodule (𝓞 F) (Fin n → F), Submodule.IsFullLattice F Λ ∧ ∀ γ : GL (Fin n) F,
        (∀ y, (γ : Matrix (Fin n) (Fin n) F) *ᵥ y ∈ Λ ↔ y ∈ Λ) →
          s⁻¹ * PIW.ClassFinD.glIncl F n γ * s ∈ PIW.ClassFinD.KGL F n := by
  intro F _ _ n s
  refine ⟨lat F s, lat_isLattice s, fun γ hγ => ⟨matInt_conj s γ fun y hy => (hγ y).2 hy, ?_⟩⟩
  have hinv : (s⁻¹ * PIW.ClassFinD.glIncl F n γ * s)⁻¹ = s⁻¹ * PIW.ClassFinD.glIncl F n γ⁻¹ * s := by
    rw [map_inv]; group
  rw [hinv]
  refine matInt_conj s γ⁻¹ fun y hy => ?_
  rw [← hγ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  exact hy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalBasisAdapted
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem exists_orthonormalBasis_adapted (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (I : Type) [Fintype I] [DecidableEq I] (p : I → Submodule ℂ E)
    (htop : (⨆ i, p i) = ⊤) (horth : ∀ i j, i ≠ j → p i ⟂ p j) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (ty : Fin (Module.finrank ℂ E) → I),
      ∀ i, Submodule.span ℂ (b '' {σ | ty σ = i}) = p i := by
  classical
  have hV : OrthogonalFamily ℂ (fun i => p i) (fun i => (p i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise (fun i j h => horth i j h)
  have hint : DirectSum.IsInternal p :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top p).2 ⟨hV.independent, htop⟩
  let v : ∀ i, OrthonormalBasis (Fin (Module.finrank ℂ (p i))) ℂ (p i) :=
    fun i => stdOrthonormalBasis ℂ (p i)
  let c := hint.collectedOrthonormalBasis hV v
  have hc : ∀ a : (Σ i, Fin (Module.finrank ℂ (p i))), c a = (v a.1 a.2 : E) := by
    intro a
    simp [c, DirectSum.IsInternal.collectedOrthonormalBasis, DirectSum.IsInternal.collectedBasis_coe]
  have hcard : Fintype.card (Σ i, Fin (Module.finrank ℂ (p i))) = Module.finrank ℂ E :=
    (Module.finrank_eq_card_basis c.toBasis).symm
  let e : (Σ i, Fin (Module.finrank ℂ (p i))) ≃ Fin (Module.finrank ℂ E) :=
    Fintype.equivFinOfCardEq hcard
  refine ⟨c.reindex e, fun σ => (e.symm σ).1, fun i => ?_⟩
  have himg : (c.reindex e) '' {σ | (e.symm σ).1 = i}
      = (p i).subtype '' Set.range (v i).toBasis := by
    ext x
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      rw [OrthonormalBasis.reindex_apply, hc]
      simp only [Set.mem_ofPred_eq] at hσ
      generalize e.symm σ = a at hσ
      obtain ⟨j, k⟩ := a
      subst hσ
      exact ⟨v j k, ⟨k, by simp⟩, rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨e ⟨i, k⟩, by simp, ?_⟩
      rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hc]
      simp
  rw [himg, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRestrictedFrames
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Mem

theorem cnorm_mulVec_eq_of_gram {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (M : Matrix ι μ ℂ) (N : Matrix κ μ ℂ) (h : Mᴴ * M = Nᴴ * N) (u : μ → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (M.mulVec u) = Formalism.HermitianLatticesTheory.cnorm (N.mulVec u) := by
  have key : ∀ {ι : Type} [Fintype ι] (M : Matrix ι μ ℂ),
      ((∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ (Mᴴ * M).mulVec u := by
    intro ι _ M
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    push_cast
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
  have h2 : (∑ i, ‖M.mulVec u i‖ ^ 2 : ℝ) = ∑ i, ‖N.mulVec u i‖ ^ 2 := by
    have := key M
    rw [h, ← key N] at this
    exact_mod_cast this
  unfold Formalism.HermitianLatticesTheory.cnorm
  rw [h2]

theorem exists_restricted_frames : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (A : HLat K)
    (U : Submodule K A.V) (L : Submodule (𝓞 K) U), (∀ v, IsUnit (A.X v).det) →
    ∃ (n : ℕ) (b : Module.Basis (Fin n) K U) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
      (∀ v, IsUnit (X v).det) ∧
        ∀ v (x : U), Formalism.HermitianLatticesTheory.normAt b X v x = Formalism.HermitianLatticesTheory.normAt A.b A.X v (x : A.V) := by
  intro K _ _ _ A U _ hX
  have : Module.Finite K A.V := Module.Finite.of_basis A.b
  let n := Module.finrank K U
  let b : Module.Basis (Fin n) K U := Module.finBasis K U
  let E : Matrix A.ι (Fin n) K := LinearMap.toMatrix b A.b U.subtype
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  have hLE : LinearMap.toMatrix A.b b g * E = 1 := by
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  let M : InfinitePlace K → Matrix A.ι (Fin n) ℂ := fun v => (A.X v)⁻¹ * E.map v.embedding
  have hM : ∀ v, Function.Injective (M v).mulVec := by
    intro v x y hxy
    have h1 : ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v) * M v = 1 := by
      simp only [M]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.X v), Matrix.mul_nonsing_inv _ (hX v),
        Matrix.one_mul, ← Matrix.map_mul, hLE, Formalism.L2.DIV.map_one']
    have := congrArg ((LinearMap.toMatrix A.b b g).map v.embedding * A.X v).mulVec hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.one_mulVec] at this
  have hP : ∀ v, ((M v)ᴴ * M v).PosDef := fun v => Matrix.PosDef.conjTranspose_mul_self _ (hM v)
  refine ⟨n, b, fun v => Formalism.L2.DIV.frameOf ((M v)ᴴ * M v),
    fun v => (Formalism.L2.DIV.frameOfSpec n _ (hP v)).1, fun v x => ?_⟩
  have h2 := (Formalism.L2.DIV.frameOfSpec n _ (hP v)).2
  have h3 : Formalism.HermitianLatticesTheory.vecAt A.b v (x : A.V) = (E.map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    have h4 := LinearMap.toMatrix_mulVec_repr b A.b U.subtype x
    funext i
    have h5 := congrFun h4 i
    simp only [Submodule.subtype_apply] at h5
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← h5]
    simp [Matrix.mulVec, dotProduct, E, Formalism.HermitianLatticesTheory.vecAt]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  rw [h3, Matrix.mulVec_mulVec]
  exact cnorm_mulVec_eq_of_gram _ _ h2 _

end GlobalTheory.Mem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingHomOfIsIntegral
section
namespace GlobalTheory.RingHomOfIsIntegral

theorem exists_ringHom_of_isIntegral (R : Type) [CommRing R] [CharZero R] [Algebra.IsIntegral ℤ R]
    (l : ℕ) [hl : Fact (Nat.Prime l)] : Nonempty (R →+* AlgebraicClosure (ZMod l)) := by
  have hinj : Function.Injective (algebraMap ℤ R) := (algebraMap ℤ R).injective_int
  have hlp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hl.out)
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R)
    (Ideal.span {(l : ℤ)}) ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [hinj (hx.trans (map_zero _).symm)]
      exact Ideal.zero_mem _)
  have := hP
  have hl0 : ((l : ℕ) : R ⧸ P) = 0 := by
    have h1 : (l : ℤ) ∈ P.comap (algebraMap ℤ R) := by
      change (l : ℤ) ∈ Ideal.under ℤ P
      rw [hPc]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at h1
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    simpa using h1
  have hchar : CharP (R ⧸ P) l := (CharP.charP_iff_prime_eq_zero hl.out).mpr hl0
  let : Algebra (ZMod l) (R ⧸ P) := ZMod.algebra _ l
  have : Algebra.IsIntegral (ZMod l) (R ⧸ P) := ⟨fun x => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ((Algebra.IsIntegral.isIntegral (R := ℤ) r).map (Ideal.Quotient.mkₐ ℤ P)).tower_top⟩
  exact ⟨(IsAlgClosed.lift (R := ZMod l) (S := R ⧸ P)
    (M := AlgebraicClosure (ZMod l))).toRingHom.comp (Ideal.Quotient.mk P)⟩

theorem nonempty_ringHom : ∀ (l : ℕ) [Fact (Nat.Prime l)],
    Nonempty (↥(integralClosure ℤ ℂ) →+* Formalism.CyclotomicNorms.Fbar l) := by
  intro l _
  exact exists_ringHom_of_isIntegral (integralClosure ℤ ℂ) l

end GlobalTheory.RingHomOfIsIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_subsingleton_coh_twist_tens_lbPow : ∀ (k : Type) [Field k] {Y : Scheme.{0}} (f : Y ⟶ Sp k), IsProjOver f → ∀ (A N : LB Y), IsAmpleLB A → N.IsLB → ∀ (G : Y.Modules) [IsFiniteQC G] (B : ℕ), ∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < B → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
  intro k _ Y f hf A N hA hN G _ B
  letI := algebraΓOfHom f
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  have H (m : Fin B) : ∃ q : ℕ, ∀ n ≥ q, ∀ p, 0 < p →
      Subsingleton (coh (twist (twist G (lbPow N m)) (lbPow A n)) p) :=
    have := isFiniteQC_twist (F := G) (isLB_lbPow hN m)
    eventually_atTop.1 (hA.eventually_subsingleton_coh_twist (f := f) (fun _ => rfl) _)
  choose q hq using H
  obtain ⟨Q, hQ⟩ := Finite.exists_le q
  refine ⟨Q, fun j m hj hm p hp => ?_⟩
  have := hq ⟨m, hm⟩ j ((hQ _).trans hj) p hp
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq G (isLB_lbPow hN m)
    (isLB_lbPow hA.isLB j) (isLB_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)) (by
      rw [cls_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m),
        ← cls_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m) (isLB_tens (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)),
        ← cls_tens (isLB_lbPow hN m) (isLB_lbPow hA.isLB j) (isLB_tens (isLB_lbPow hN m) (isLB_lbPow hA.isLB j))]
      exact (cls_eq_iff _ _).2 (tens_comm_iso (isLB_lbPow hA.isLB j) (isLB_lbPow hN m)))
  exact (cohOn.mapIso k ⊤ p e).symm.injective.subsingleton

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaComparisonDataIndependentOfAlgebraicForms
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo


set_option maxHeartbeats 1600000 in
theorem omDat_updFW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), ∃ O' : OMDat T.toCore (updFW R nW FW) i Tp tup, O'.c' = O.c' ∧ O'.lev = O.lev ∧ (O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) → O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀)) ∧ ∀ (cc : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (ph : ℂ), O.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph → O'.OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ nW FW i Tp tup O
  refine ⟨{ O with }, rfl, rfl, fun h => ?_, fun cc ph h => h⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

end GlobalTheory.RealGeo
end

