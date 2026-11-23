module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntertwiningOfCentralFiltrationStep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

namespace CentralSplit

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

noncomputable def prodOp (ρ : Representation ℂ G V) (z : G) (a : ℕ → ℂ) : ℕ → Module.End ℂ V
  | 0 => 1
  | m + 1 => prodOp ρ z a m * (ρ z - a m • 1)

noncomputable def prodScal (c : ℂ) (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => prodScal c a m * (c - a m)

theorem prodOp_succ_apply (ρ : Representation ℂ G V) (z : G) (a : ℕ → ℂ) (m : ℕ) (v : V) :
    prodOp ρ z a (m + 1) v = prodOp ρ z a m (ρ z v - a m • v) := by
  simp [prodOp]

theorem prodOp_comm (ρ : Representation ℂ G V) (z : G) (hz : ∀ g, g * z = z * g) (a : ℕ → ℂ)
    (m : ℕ) (g : G) (v : V) : prodOp ρ z a m (ρ g v) = ρ g (prodOp ρ z a m v) := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    have hzg : ρ z (ρ g v) = ρ g (ρ z v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← hz, map_mul, Module.End.mul_apply]
    rw [prodOp_succ_apply, prodOp_succ_apply, hzg, ← LinearMap.map_smul (ρ g),
      ← LinearMap.map_sub (ρ g), ih]

theorem prodScal_ne_zero (c : ℂ) (a : ℕ → ℂ) (M : ℕ) (h : ∀ m < M, a m ≠ c) :
    ∀ m ≤ M, prodScal c a m ≠ 0 := by
  intro m hm
  induction m with
  | zero => simp [prodScal]
  | succ m ih =>
    simp only [prodScal]
    exact mul_ne_zero (ih (by omega)) (sub_ne_zero.2 (h m (by omega)).symm)

end CentralSplit


open CentralSplit in
theorem exists_intertwining_of_central_step : ∀ {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G Y) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ (z : G), (∀ g, g * z = z * g) →
    ∀ (t₀ : Fin N) (c : ℂ) (c' : Fin N → ℂ), (∀ t, t ≠ t₀ → c' t ≠ c) →
    (∀ t, t ≠ t₀ → ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' t • y) →
    Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv τ) → (∀ y, τ z y = c • y) → Nontrivial Y →
    ∃ (φ : ρ.IntertwiningMap τ) (v : V), φ v ≠ 0 := by
  intro G V Y _ _ _ _ _ ρ τ N S _ _ htop z hz t₀ c c' hc' hstep hΨ hτ _
  obtain ⟨Ψ⟩ := hΨ
  set B := S t₀.succ with hBdef
  set A := S t₀.castSucc with hAdef
  let a : ℕ → ℂ := fun i => if h : i < N then c' ⟨i, h⟩ else 0
  let M := N - (t₀.val + 1)

  have hZ : ∀ y, subQuot B A z y = c • y := by
    intro y
    apply Ψ.toLinearEquiv.injective
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap z y
    rw [Representation.Equiv.toLinearEquiv_apply, h1, hτ, map_smul, Representation.Equiv.toLinearEquiv_apply]
  have ha : ∀ m (hm : t₀.val + 1 + m < N), a (t₀.val + 1 + m) = c' ⟨t₀.val + 1 + m, by omega⟩ := by
    intro m hm; simp [a, hm]

  have L1 : ∀ m, ∀ (h : t₀.val + 1 + m < N + 1), ∀ v, v ∈ (S ⟨t₀.val + 1 + m, h⟩).toSubmodule →
      prodOp ρ z (fun i => a (t₀.val + 1 + i)) m v ∈ B.toSubmodule := by
    intro m
    induction m with
    | zero =>
      intro h v hv
      have e : (⟨t₀.val + 1 + 0, h⟩ : Fin (N + 1)) = t₀.succ := by ext; simp
      rw [e] at hv
      exact hv
    | succ m ih =>
      intro h v hv
      let t : Fin N := ⟨t₀.val + 1 + m, by omega⟩
      have ht : t ≠ t₀ := fun e => by have := congrArg Fin.val e; simp only [t] at this; omega
      have hvs : v ∈ (S t.succ).toSubmodule := by
        have : t.succ = ⟨t₀.val + 1 + (m + 1), h⟩ := by ext; simp [t]; omega
        rw [this]; exact hv
      have hq := hstep t ht (Submodule.Quotient.mk ⟨v, hvs⟩)
      have hmem : ρ z v - c' t • v ∈ (S t.castSucc).toSubmodule := by
        have e2 : subQuot (S t.succ) (S t.castSucc) z (Submodule.Quotient.mk ⟨v, hvs⟩) =
            Submodule.Quotient.mk ⟨ρ z v, (S t.succ).apply_mem_toSubmodule z hvs⟩ := rfl
        rw [e2, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hq
        simpa using hq
      rw [prodOp_succ_apply]
      have e3 : a (t₀.val + 1 + m) = c' t := ha m (by omega)
      simp only [e3]
      exact ih (by omega) _ hmem

  have L2 : ∀ m, ∀ b (hb : b ∈ B.toSubmodule), ∃ h' : prodOp ρ z (fun i => a (t₀.val + 1 + i)) m b ∈ B.toSubmodule,
      (Submodule.Quotient.mk ⟨_, h'⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) =
        prodScal c (fun i => a (t₀.val + 1 + i)) m • Submodule.Quotient.mk ⟨b, hb⟩ := by
    intro m
    induction m with
    | zero => intro b hb; exact ⟨hb, by simp [prodOp, prodScal]⟩
    | succ m ih =>
      intro b hb
      have hb' : ρ z b - a (t₀.val + 1 + m) • b ∈ B.toSubmodule :=
        B.toSubmodule.sub_mem (B.apply_mem_toSubmodule z hb) (B.toSubmodule.smul_mem _ hb)
      obtain ⟨h', e⟩ := ih _ hb'
      refine ⟨by rw [prodOp_succ_apply]; exact h', ?_⟩
      have e4 : (Submodule.Quotient.mk ⟨_, hb'⟩ : B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) =
          (c - a (t₀.val + 1 + m)) • Submodule.Quotient.mk ⟨b, hb⟩ := by
        have e5 : subQuot B A z (Submodule.Quotient.mk ⟨b, hb⟩) =
            Submodule.Quotient.mk ⟨ρ z b, B.apply_mem_toSubmodule z hb⟩ := rfl
        rw [sub_smul, ← hZ, e5, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub]
        rfl
      simp only [prodOp_succ_apply, prodScal]
      rw [mul_smul, ← e4, ← e]
  set op := prodOp ρ z (fun i => a (t₀.val + 1 + i)) M with hop
  have hNM : t₀.val + 1 + M = N := by omega
  have hM : ∀ v, op v ∈ B.toSubmodule := by
    intro v
    refine L1 M (by omega) v ?_
    have e : (⟨t₀.val + 1 + M, by omega⟩ : Fin (N + 1)) = Fin.last N := by ext; simp [hNM]
    rw [e, htop]
    trivial
  have hlam : prodScal c (fun i => a (t₀.val + 1 + i)) M ≠ 0 := by
    refine prodScal_ne_zero c _ M (fun m hm => ?_) M le_rfl
    show a (t₀.val + 1 + m) ≠ c
    rw [ha m (by omega)]
    exact hc' _ (fun e => by have := congrArg Fin.val e; simp only at this; omega)
  let φlin : V →ₗ[ℂ] Y := Ψ.toLinearMap ∘ₗ (A.toSubmodule.comap B.toSubmodule.subtype).mkQ ∘ₗ
    LinearMap.codRestrict B.toSubmodule op hM
  have hφ : ∀ g v, φlin (ρ g v) = τ g (φlin v) := by
    intro g v
    have e6 : (LinearMap.codRestrict B.toSubmodule op hM) (ρ g v) =
        B.toRepresentation g (LinearMap.codRestrict B.toSubmodule op hM v) :=
      Subtype.ext (prodOp_comm ρ z hz _ M g v)
    show Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ op hM (ρ g v))) =
      τ g (Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ op hM v)))
    have e8 : Submodule.mkQ (A.toSubmodule.comap B.toSubmodule.subtype)
        (B.toRepresentation g (LinearMap.codRestrict B.toSubmodule op hM v)) =
        subQuot B A g (Submodule.mkQ _ (LinearMap.codRestrict B.toSubmodule op hM v)) := rfl
    rw [e6, e8]
    exact Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap g _
  refine ⟨φlin.intertwiningMap_of_isIntertwiningMap ρ τ hφ, ?_⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨⟨b, hb⟩, hx⟩ := Submodule.Quotient.mk_surjective _ (Ψ.toLinearEquiv.symm y)
  obtain ⟨h', e⟩ := L2 M b hb
  refine ⟨b, ?_⟩
  rw [LinearMap.toIntertwiningMap]
  have e7 : φlin b = Ψ.toLinearEquiv (Submodule.Quotient.mk ⟨op b, h'⟩) := rfl
  rw [e7, e, hx, map_smul, LinearEquiv.apply_symm_apply]
  exact smul_ne_zero hlam hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeTame

def invTranspose {R : Type} [CommRing R] (n : ℕ) : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨(g⁻¹).val.transpose, g.val.transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invTranspose_val {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    (invTranspose n g).val = (g⁻¹).val.transpose := rfl

theorem invTranspose_inv_val {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    ((invTranspose n g)⁻¹).val = g.val.transpose := rfl

theorem invTranspose_invTranspose {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    invTranspose n (invTranspose n g) = g := by
  apply Units.ext
  rw [invTranspose_val, invTranspose_inv_val, Matrix.transpose_transpose]

theorem continuous_invTranspose {R : Type} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    Continuous (invTranspose (R := R) n) := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem invTranspose_mem_GLint {F : Type} [Field F] (n : ℕ) (O : Subring F) {g : GL (Fin n) F}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) : invTranspose n g ∈ Formalism.UG.GLint (Fin n) O := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨invTranspose n h, Units.ext rfl⟩

theorem conjSP_proj {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (x : AL L) :
    (conjSP s).proj x = s.proj (conjAL L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

theorem conjSP_loc {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (κ : GA L n) :
    (conjSP s).loc n κ = invTranspose n (s.loc n κ) := by
  have hm : κ.1.val * conjT (conjAL L) κ.1.val = 1 := κ.2
  have h1 : (κ.1⁻¹).val = conjT (conjAL L) κ.1.val := Units.inv_eq_of_mul_eq_one_right hm
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (conjSP s).proj (κ.1.val i j) = s.proj ((κ.1⁻¹).val j i)
  rw [h1, conjSP_proj]
  rfl

theorem exists_conj_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∃ (K' : Subgroup (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L)))) (θ' : K' →* ℂˣ), (∀ g ∈ K', g ∈ Formalism.UG.GLint (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ'.ker : Set K') ∧ (∀ κ : GAf L n, (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K' ↔ s.loc n κ ∈ K) ∧ (∀ (κ : GAf L n) (h : s.loc n κ ∈ K) (h' : (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K'), θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc n κ, h'⟩ = θ ⟨s.loc n κ, h⟩) ∧ ∀ g (hg : g ∈ K) (g' : GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L))), g'.val = (g⁻¹).val.transpose → ∃ h' : g' ∈ K', θ' ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
  intro L _ _ _ n s K θ hK hθ
  have key : ∀ (g' : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g) (hg : g ∈ K),
      g' = invTranspose n g → ∃ h' : g' ∈ K.comap (invTranspose n),
        θ.comp ((invTranspose n).subgroupComap K) ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
    rintro g' g hg rfl
    refine ⟨by rw [Subgroup.mem_comap, invTranspose_invTranspose]; exact hg, ?_⟩
    rw [MonoidHom.comp_apply]
    exact congrArg θ (Subtype.ext (invTranspose_invTranspose n g))
  refine ⟨K.comap (invTranspose n), θ.comp ((invTranspose n).subgroupComap K), ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have := invTranspose_mem_GLint n _ (hK _ hg)
    rwa [invTranspose_invTranspose] at this
  · have hc : Continuous ((invTranspose n).subgroupComap K) :=
      Continuous.subtype_mk ((continuous_invTranspose n).comp continuous_subtype_val) _
    exact hθ.preimage hc
  · intro κ
    rw [conjSP_loc]
    change invTranspose n (invTranspose n (s.loc n κ)) ∈ K ↔ _
    rw [invTranspose_invTranspose]
  · intro κ h h'
    exact (key _ _ h (conjSP_loc n s κ)).2
  · intro g hg g' hg'
    exact key g' g hg (Units.ext hg')

end GlobalTheory.TypeTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDatumExist

open scoped TensorProduct

theorem isCMExt (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
  ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
    fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩

theorem mem_tensInt_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    x ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (Formalism.UG.Ov F v) ↔
      Algebra.TensorProduct.comm F E (v.adicCompletion F) x ∈ GlobalTheory.AdelicU.intLoc F E v := by
  constructor
  · intro hx
    have hle : Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (Formalism.UG.Ov F v) ≤
        (GlobalTheory.AdelicU.intLoc F E v).comap (Algebra.TensorProduct.comm F E (v.adicCompletion F)).toRingHom := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · show Algebra.TensorProduct.comm F E _ (((a : E)) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ GlobalTheory.AdelicU.intLoc F E v
        rw [Algebra.TensorProduct.comm_tmul]
        exact GlobalTheory.AdelicU.tmul_mem_intLoc (one_mem _) a
      · show Algebra.TensorProduct.comm F E _ ((1 : E) ⊗ₜ[F] y) ∈ GlobalTheory.AdelicU.intLoc F E v
        rw [Algebra.TensorProduct.comm_tmul]
        have := GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) hy (1 : 𝓞 E)
        simpa using this
    exact hle hx
  · intro hx
    have h := GlobalTheory.AdelicU.intLoc_induction
      (p := fun y => (Algebra.TensorProduct.comm F E (v.adicCompletion F)).symm y ∈
        Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (Formalism.UG.Ov F v))
      (fun a ha z => by
        have e1 : (Algebra.TensorProduct.comm F E (v.adicCompletion F)).symm (a ⊗ₜ[F] (z : E)) =
            ((z : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] a) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rfl
        rw [e1]
        exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨(z : E), z, rfl⟩, rfl⟩))
          (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)))
      (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)
      (fun y hy => by rw [map_neg]; exact neg_mem hy) hx
    simpa using h

theorem exists_inertDatum : ∀ (D : D7) (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))),
    (∀ s : SplitPlace D.host.E, s.v ≠ v) → ∃ w : HeightOneSpectrum (𝓞 D.host.E), NG.OverPl w v ∧
      ¬ IsSplitPl D.host w ∧ Nonempty (InertDatum D.host.E n v w) := by
  intro D n v hv
  classical
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ.isPrime, fun h0 => v.ne_bot (by
    rw [hQv.over, h0]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _))⟩
  have hov : NG.OverPl w v := hQv.over.symm
  have hunder : w.under (𝓞 (maximalRealSubfield D.host.E)) = v := HeightOneSpectrum.ext hov
  have key : ∀ x ∈ w.asIdeal, IsCMField.ringOfIntegersComplexConj D.host.E x ∈ w.asIdeal := by
    intro x hx
    by_contra hc
    have hspl : IsSplitPl D.host w := ⟨x, hx, fun y hy hym => hc (by
      have : y = IsCMField.ringOfIntegersComplexConj D.host.E x := by
        apply RingOfIntegers.ext
        rw [hy, IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.SplitPlaceOver.host_conj_eq']
      simpa [this] using hym)⟩
    obtain ⟨s, ϖ, hs, hϖ⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hspl
    apply hv s
    apply HeightOneSpectrum.ext
    rw [← s.w_under, ← hov]
    ext a
    have ha : D.host.conj ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
        ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) := by
      rw [GlobalTheory.SplitPlaceOver.host_conj_eq']
      exact congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ((IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).2 ⟨a, rfl⟩)
    exact (hs _ _ ha.symm).symm
  have hnsp : ¬ IsSplitPl D.host w := by
    rintro ⟨x, hx, hy⟩
    exact hy _ (by rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.SplitPlaceOver.host_conj_eq']) (key x hx)
  have hnsa : ¬ GlobalTheory.UnitaryBC.IsSplitAt w := by
    rintro ⟨u, hne, hu⟩
    apply hne
    apply HeightOneSpectrum.ext
    apply u.isMaximal.eq_of_le w.isPrime.ne_top
    intro x hx
    by_contra hxw
    have hfix : IsCMField.ringOfIntegersComplexConj D.host.E (x * IsCMField.ringOfIntegersComplexConj D.host.E x) =
        x * IsCMField.ringOfIntegersComplexConj D.host.E x := by
      apply RingOfIntegers.ext
      simp [IsCMField.coe_ringOfIntegersComplexConj, mul_comm]
    obtain ⟨a, ha⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
    have hcom := congrArg HeightOneSpectrum.asIdeal hu
    change u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) at hcom
    have hp : a ∈ u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      change algebraMap _ _ a ∈ u.asIdeal
      rw [ha]; exact u.asIdeal.mul_mem_right _ hx
    rw [hcom] at hp
    change algebraMap _ _ a ∈ w.asIdeal at hp
    rw [ha] at hp
    rcases w.isPrime.mem_or_mem hp with h | h
    · exact hxw h
    · apply hxw
      have hh := key _ h
      have he : IsCMField.ringOfIntegersComplexConj D.host.E (IsCMField.ringOfIntegersComplexConj D.host.E x) = x := by
        apply RingOfIntegers.ext
        simp [IsCMField.coe_ringOfIntegersComplexConj]
      rwa [he] at hh
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield D.host.E) D.host.E v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w (GlobalTheory.DefiniteBC.host_unramified D.host w) hnsa
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj D.host.E).toAlgHom hw hunder
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (isCMExt D.host.E) hw hc
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov D.host.E w = Formalism.UG.intL (w.adicCompletion D.host.E) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield D.host.E) D.host.E
    (v.adicCompletion (maximalRealSubfield D.host.E))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  refine ⟨w, hov, hnsp, ⟨⟨e, c, ϖ, k, ?_, hU, ?_, ?_, ?_⟩⟩⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj D.host.E).toAlgHom _ x)) =
      c (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro x
    rw [mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · rw [← hO]; exact hk
  · simpa using hke

end GlobalTheory.InertDatumExist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRamifiedOfRamifiedLocalComponent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.VTypeTame.ramified_of_isComp : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (ξ : (w.adicCompletion E)ˣ →* ℂˣ), IsComp χ w ξ → ¬ GlobalTheory.SplitWeil.IsUnram ξ → ¬ χ.UnrAt w := by
  intro E _ _ χ w ξ hξ hn hu
  have hc : IsComp χ w (χ.loc w) := ⟨GlobalTheory.HeckeComp.smooth_loc χ w, fun _ => rfl⟩
  have he : ξ = χ.loc w := GlobalTheory.HeckeComp.eq_of_isComp hc hξ
  apply hn
  intro x hx
  rw [he]
  apply hu x
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  show Valued.v (x : w.adicCompletion E) = 1
  exact h1.eq_one_iff_eq_one.1 hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLongOrbitWordConditionsOfLargeScale
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem jointB_of_large : ∀ eps ez C₂ A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L)
    (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D →
    (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointB L HW C₂ := by
  intro eps ez C₂ A heps hez
  obtain ⟨x1, h1⟩ := GlobalTheory.HTW.roomy_of_large eps (max 100 (2 * C₂)) A heps (le_max_left _ _)
  obtain ⟨x2, h2⟩ := GlobalTheory.InertPrimeEleven.eleven_le ez hez
  refine ⟨max x1 x2, ?_⟩
  intro D L Pm HW hE hZ hA hx hadm hfont hJ i hin hrow r ρ π hPt w hw
  have hR : Roomy L (max 100 (2 * C₂)) := h1 D L Pm hE hA (le_trans (le_max_left _ _) hx)
  have h11 : 11 ≤ D.nd.l i :=
    h2 D L (D.nd.l i) hZ (le_trans (le_max_right _ _) hx) Fact.out hin
  refine ⟨_root_.GlobalTheory.bridge_field_le_unramified D.nbr i w hw hin.1 hin.2.1 hin.2.2.1, ?_⟩
  intro Cx hG
  obtain ⟨ε, g, hg, hB⟩ := GlobalTheory.T.wordConditions_common_natural_representation L _ HW i r ρ π w hw Cx hG hR hadm hfont hJ hPt hin.1 hin.2.1 hin.2.2.1
  have hWB : WordsB L (D.nd.l i) C₂ (recWord L (liftIdx D i) ε g) := by
    refine _root_.GlobalTheory.HTW.Rec.wordsB_recWord_of_long_orbit L Pm _ C₂ _ ε g _ (D.nd.l i) hR hg (le_max_right _ _) h11 hrow.1 ?_
    rw [Prod.snd_inv, orderOf_inv]
    exact hrow.lt_orderOf
  refine ⟨_, hB, _root_.GlobalTheory.HTW.RecS.setting_of_wordBase L HW i r ρ π w hw Cx hG _ hin.ne_two hB, h11, hWB.j_lt, hWB.par, ?_⟩
  intro t ht
  exact _root_.GlobalTheory.HTW.Rec.clusters_letterwise _ _ hWB.clusters t ht

end GlobalTheory.HTW.RecS
end

