module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupCharacterEqOneOfTrivialIntegral
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictTranslatedDiagonalMem
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.DiagShift

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField


variable (F κ) in
def diagA : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => Sum.elim x x
      map_add' := fun x x' => by funext i; cases i <;> simp
      map_smul' := fun c x => by funext i; cases i <;> simp }

theorem diagA_apply (x : κ → mixedEmbedding.mixedSpace F) : diagA F κ x = Sum.elim x x := rfl

theorem norm_le_diagA (x : κ → mixedEmbedding.mixedSpace F) : ‖x‖ ≤ ‖diagA F κ x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by
    simpa [diagA_apply] using norm_le_pi_norm (diagA F κ x) (Sum.inl j)


variable (F κ) in
def restrA : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.compCLM ℂ (diagA F κ).hasTemperateGrowth
    ⟨1, 1, fun x => by
      have := norm_le_diagA x
      have h0 := norm_nonneg (diagA F κ x)
      rw [pow_one, one_mul]; linarith⟩

theorem restrA_apply (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) (x : κ → mixedEmbedding.mixedSpace F) :
    restrA F κ f x = f (Sum.elim x x) := rfl

theorem shift_mem_finite {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)) (b : κ → FiniteAdeleRing (𝓞 F) F) :
    (fun y : κ → FiniteAdeleRing (𝓞 F) F => g (Sum.elim (y + b) y)) ∈ finiteSchwartzBruhatPi F := by
  have hd : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      (Sum.elim (y + b) y : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
    continuous_pi fun i => by
      cases i with
      | inl j => exact (continuous_apply j).add continuous_const
      | inr j => exact continuous_apply j
  have hr : Continuous fun z : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F => fun j => z (Sum.inr j) :=
    continuous_pi fun j => continuous_apply _
  refine ⟨hg.1.comp_continuous hd, ?_⟩
  refine HasCompactSupport.intro (hg.2.isCompact.image hr) fun y hy => ?_
  by_contra h
  exact hy ⟨Sum.elim (y + b) y, subset_tsupport _ h, rfl⟩

theorem shift_pureA_mem (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F))
    (u : κ → AdeleRing (𝓞 F) F) :
    (fun t : κ → AdeleRing (𝓞 F) F => pureA F f g (Sum.elim (t + u) t)) ∈ schwartzBruhatPi (K := F) (ι := κ) := by
  have key : (fun t : κ → AdeleRing (𝓞 F) F => pureA F f g (Sum.elim (t + u) t)) =
      schwartzBruhatTensorPi
        (restrA F κ (SchwartzMap.compSubConstCLM ℂ (-Sum.elim (infPartPi u) 0) f))
        (fun y : κ → FiniteAdeleRing (𝓞 F) F => g (Sum.elim (y + finPartPi u) y)) := by
    funext t
    simp only [schwartzBruhatTensorPi, restrA_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
    unfold pureA
    congr 1
    · congr 1
      funext i
      cases i with
      | inl j => exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (t j).1 (u j).1
      | inr j => exact (add_zero _).symm
    · congr 1
      funext i
      cases i <;> rfl
  rw [key]
  exact schwartzBruhatTensorPi_mem _ (shift_mem_finite hg _)

theorem shift_mem_schwartzBruhatPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (φ : (κ ⊕ κ → AF F) → ℂ) (hφ : φ ∈ schA F (κ ⊕ κ)) (u : κ → AF F) :
    (fun t : κ → AF F => φ (Sum.elim (t + u) t)) ∈ schwartzBruhatPi (K := F) (ι := κ) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact shift_pureA_mem f hg u
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.DiagShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
section
noncomputable section

namespace GlobalTheory.InertChar

section CM

open Formalism.UG Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp GlobalTheory.SelfDualGenus
  GlobalTheory.InertDoubleCoset
open scoped TensorProduct Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem core (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {P : HeightOneSpectrum (𝓞 E)}
    {e : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E} (he : IsIdemOf E v e)
    (hin : IsInertAt (maximalRealSubfield E) E v P) (h2 : (2 : 𝓞 E) ∉ P.asIdeal)
    (ν : HA (AF (maximalRealSubfield E)) hc.sig V.gram →* Circle)
    (hν : ∀ k, Supp hc V e k → Stab hc V k → ν k = 1) (g : HA (AF (maximalRealSubfield E)) hc.sig V.gram)
    (hg : Supp hc V e g) : ν g = 1 := by
  have hur := unramified hc
  obtain ⟨σ, π, hσE, hσ⟩ := GlobalTheory.FixedPrime.exists_isUnramInv v P hin
  obtain ⟨ψ, hψE, hψσ, hψO⟩ := _root_.GlobalTheory.InertCompletion.exists_ringEquiv_completion E v P hin σ hσE hσ.2.1
  obtain ⟨h, hfr, hon⟩ := exists_orthonormal hc V v
  obtain ⟨s1, s2, s3⟩ := _root_.GlobalTheory.SuppLocal.supp_local _ E hc V v e he
  let ψ' : LocAlg v →+* P.adicCompletion E := ψ
  let φ : HA (AF (maximalRealSubfield E)) hc.sig V.gram →* GL (Fin V.rank) (P.adicCompletion E) :=
    (bc ψ').comp ((MulAut.conj h⁻¹).toMonoidHom.comp (locMat hc V v))
  have hφ : ∀ k, φ k = bc ψ' (h⁻¹ * locMat hc V v k * h) := fun k => rfl
  have hO : ∀ z, z ∈ ordAt E v ↔ ψ' z ∈ intL (P.adicCompletion E) := fun z => (mem_ordAt_iff v z).trans (hψO z)
  have hback : ∀ x : GL (Fin V.rank) (LocAlg v), bc (ψ.symm : P.adicCompletion E →+* LocAlg v) (bc ψ' x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.symm_apply_apply _)
  have hback' : ∀ x : GL (Fin V.rank) (P.adicCompletion E),
      bc ψ' (bc (ψ.symm : P.adicCompletion E →+* LocAlg v) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have hmem : ∀ k, φ k ∈ UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)) := fun k =>
    bc_mem_UJ_one (σ := locConj v) ψ' hψσ (conj_mem_UJ _ hon (locMat_mem hc V v k))
  have hinj : ∀ k, Supp hc V e k → ∀ k', Supp hc V e k' → φ k = φ k' → k = k' := fun k hk k' hk' e => by
    refine s2 k k' hk hk' ?_
    have := congrArg (bc (ψ.symm : P.adicCompletion E →+* LocAlg v)) e
    rw [hφ, hφ, hback, hback] at this
    exact mul_left_cancel (mul_right_cancel this)
  have hsurj : ∀ u : UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)),
      ∃ k, Supp hc V e k ∧ φ k = u := fun ⟨u, hu⟩ => by
    have h1 := bc_mem_UJ_one (σ' := locConj v) (ψ.symm : P.adicCompletion E →+* LocAlg v)
      (fun z => ψ.injective (by
        rw [hψσ]
        exact (ψ.apply_symm_apply _).trans (congrArg σ (ψ.apply_symm_apply _).symm))) hu
    obtain ⟨k, hk, ek⟩ := s3 _ (conj_mem_UJ _ (inv_frame _ hon) h1)
    refine ⟨k, hk, ?_⟩
    show φ k = u
    rw [hφ, ek, ← hback' u]
    congr 1
    rw [hback']
    group
  have hmul : ∀ k k', Supp hc V e k → Supp hc V e k' → Supp hc V e (k * k') := fun k k' hk hk' => by
    obtain ⟨a1, a2⟩ := (s1 k).1 hk
    obtain ⟨b1, b2⟩ := (s1 k').1 hk'
    refine (s1 _).2 ⟨?_, fun w hw => by rw [map_mul, a2 w hw, b2 w hw, one_mul]⟩
    exact (map_mul (bc (infP (maximalRealSubfield E) E)) (HA.mat _ hc.sig V.gram k)
      (HA.mat _ hc.sig V.gram k')).trans (by rw [a1, b1, one_mul])
  choose l hl1 hl2 using hsurj
  let μ : UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)) →* Circle :=
    MonoidHom.mk' (fun u => ν (l u)) fun a b => by
      rw [← map_mul, hinj _ (hl1 _) _ (hmul _ _ (hl1 a) (hl1 b)) (by rw [map_mul, hl2, hl2, hl2]; rfl)]
  have hv2 : Valued.v (2 : P.adicCompletion E) = 1 := by
    rw [← map_ofNat (algebraMap E (P.adicCompletion E)) 2, GlobalTheory.Idele.valued_algebraMap,
      ← map_ofNat (algebraMap (𝓞 E) E) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_eq_one_iff).2 h2
  have : CharZero (P.adicCompletion E) := algebraRat.charZero _
  have key := _root_.GlobalTheory.UnitaryCharacter.char_eq_one (P.adicCompletion E) π σ _ V.rank 1 hσ hv2 (one_mem _)
    (fun i j => by
      simp only [Units.val_one, Matrix.one_apply, eq_comm (a := j)]
      split_ifs
      · exact map_one σ
      · exact map_zero σ) μ
    (fun k hk => hν _ (hl1 k) ((GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral _ E hc V v h hfr _ ((s1 _).1 (hl1 k)).2).2
      ((bc_mem_range_iff ψ' hO _).2 (by rw [← hφ, hl2]; exact hk)))) ⟨φ g, hmem g⟩
  rw [hinj g hg _ (hl1 ⟨φ g, hmem g⟩) (hl2 ⟨φ g, hmem g⟩).symm]
  exact key

end CM

section Lattice

open Formalism.BasicNotions NumberField

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mem_dual (V : HSpace E) (L : Submodule (𝓞 E) V.V) (z : V.V) :
    z ∈ Formalism.HermitianLatticesTheory.dual V.hT L ↔ ∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = V.hT y z := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one,
    LinearMap.restrictScalars_apply]

def withLat (V : HSpace E) (Λ : Submodule (𝓞 E) (Fin V.rank → E)) (h1 : Submodule.IsLattice E Λ)
    (h2 : ∀ y : Fin V.rank → E, y ∈ Λ ↔
      ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * V.gram i j * y j) : HSpace E :=
  let f : (Fin V.rank → E) →ₗ[𝓞 E] V.V :=
    V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 E)
  let L : Submodule (𝓞 E) V.V := Λ.map f
  have hL : Formalism.HermitianLatticesTheory.dual V.hT L = L := by
    refine Submodule.ext fun z => (mem_dual V L z).trans ?_
    obtain ⟨y, rfl⟩ := V.frame.equivFun.symm.surjective z
    constructor
    · intro h
      refine ⟨y, (h2 y).2 fun x hx => ?_, rfl⟩
      rw [← GlobalTheory.WeilUnramifiedCompare.hT_coord, ← V.frame.equivFun_symm_apply, ← V.frame.equivFun_symm_apply]
      exact h _ ⟨x, hx, rfl⟩
    · rintro ⟨y', hy, e⟩ _ ⟨x, hx, rfl⟩
      obtain rfl : y' = y := V.frame.equivFun.symm.injective e
      have := (h2 y').1 hy x hx
      rwa [← GlobalTheory.WeilUnramifiedCompare.hT_coord, ← V.frame.equivFun_symm_apply,
        ← V.frame.equivFun_symm_apply] at this
  { V with
    L0 := L
    standardTuple_isLattice := Submodule.IsLattice.of_fg E (h1.fg.map f)
    baseLattice_isUnimodular := hL }

theorem coord_withLat (V : HSpace E) (Λ : Submodule (𝓞 E) (Fin V.rank → E)) (h1 h2) :
    {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ (withLat V Λ h1 h2).L0} = Λ := by
  ext x
  rw [Set.mem_ofPred_eq, ← V.frame.equivFun_symm_apply]
  constructor
  · rintro ⟨y, hy, e⟩
    obtain rfl : y = x := V.frame.equivFun.symm.injective e
    exact hy
  · exact fun h => ⟨x, h, rfl⟩

end Lattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem char_eq_one_of_nonSplit : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ v ε, NonSplitAt D v ε → ∀ ν : GA D V →* Circle, (∀ k, SuppPl ε V k → (∀ y, y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ (finMat D.sp.cm.sig V.gram k).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E))) → ν k = 1) → ∀ g, SuppPl ε V g → ν g = 1 := by
  intro D V Λ hΛ v ε hv ν hν g hg
  obtain ⟨⟨α, rfl, a1, a2⟩, hn⟩ := hv
  have hα : α = singleV D.host.F v 1 := GlobalTheory.SplitIdem.af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [a1, GlobalTheory.SplitIdem.evalV_singleV_same]
    · rw [a2 w hw, GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw]
  have hn' : ∀ e : Formalism.L2.Theta.AE D, e * e = e → e * cA D e = 0 → e + cA D e =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) → False :=
    fun e e1 e2 e3 => by
      rw [← hα] at e3
      exact hn ⟨e, ⟨e1, e2, v, _, ⟨α, rfl, a1, a2⟩, e3⟩, e3⟩
  have h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal := fun h2 => by
    obtain ⟨e, e1, e2, e3, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
    exact hn' e e1 e2 e3
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
        (FaithfulSMul.algebraMap_injective _ _)]
      exact bot_le)
  have hQ0 : Q ≠ ⊥ := fun h0 => v.ne_bot (by
    rw [← hQv, h0, Ideal.under_bot])
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hPv : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQv
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  have hin := GlobalTheory.FixedPrime.isInertAt_under P fun x hx => by
    by_contra hx'
    obtain ⟨e, e1, e2, e3⟩ := GlobalTheory.MovedSplit.exists_splitAt D v
      ⟨Q, hQ.isPrime, hQv, _, hx, x, (star_star (x : D.host.E)).symm, hx'⟩
    exact hn' e e1 e2 e3
  have h2' : (2 : 𝓞 D.host.E) ∉ P.asIdeal := fun h => h2 (by
    rw [← hQv, Ideal.mem_comap, map_ofNat]; exact h)
  have he := GlobalTheory.PlaceComp.isIdemOf_algebraMap (E := D.host.E) a1 a2
  subst hPv
  refine core (E := D.host.E) D.sp.cm (withLat V Λ hΛ.1 hΛ.2) he hin h2' ν (fun k hk hs => hν k hk ?_) g hg
  rw [← coord_withLat V Λ hΛ.1 hΛ.2]
  exact hs

end GlobalTheory.InertChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisHenselExistsUniqueSqrt
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan.HenselSqrt

open IsDedekindDomain.HeightOneSpectrum WithZero

variable (v : HeightOneSpectrum ℤ) {L : Type} [Field L] [NumberField L] {κ : Type}
  (bL : Module.Basis κ ℚ L)

theorem isIntB_add {x y : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsIntB v bL x) (hy : IsIntB v bL y) :
    IsIntB v bL (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_neg {x : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsIntB v bL x) : IsIntB v bL (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

theorem isIntB_smul {a : v.adicCompletion ℚ} (ha : a ∈ v.adicCompletionIntegers ℚ)
    {x : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsIntB v bL x) : IsIntB v bL (a • x) := fun i => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem ha (hx i)

theorem isSmallB_neg {x : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsSmallB v bL x) : IsSmallB v bL (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]; exact hx i

variable (h1 : IsIntB v bL 1) (hmul : ∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y))

def lam : Subring (v.adicCompletion ℚ ⊗[ℚ] L) where
  carrier := {x | IsIntB v bL x}
  mul_mem' := fun {x y} hx hy => hmul x y hx hy
  one_mem' := h1
  add_mem' := fun hx hy => isIntB_add v bL hx hy
  zero_mem' := isIntB_zero v bL
  neg_mem' := fun hx => isIntB_neg v bL hx

def unif (π : v.adicCompletionIntegers ℚ) : lam v bL h1 hmul :=
  ⟨(π : v.adicCompletion ℚ) • 1, isIntB_smul v bL π.2 h1⟩

variable (π : v.adicCompletionIntegers ℚ) (hπ : Valued.v (π : v.adicCompletion ℚ) = exp (-1 : ℤ))
include hπ

theorem mem_pow_iff (x : lam v bL h1 hmul) (n : ℕ) :
    x ∈ (Ideal.span {unif v bL h1 hmul π}) ^ n • (⊤ : Submodule (lam v bL h1 hmul) (lam v bL h1 hmul)) ↔
      ∀ i, Valued.v ((Algebra.TensorProduct.basis (v.adicCompletion ℚ) bL).repr (x : v.adicCompletion ℚ ⊗[ℚ] L) i)
        ≤ exp (-(n : ℤ)) := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hc : ((unif v bL h1 hmul π ^ n : lam v bL h1 hmul) : v.adicCompletion ℚ ⊗[ℚ] L) =
      (π : v.adicCompletion ℚ) ^ n • (1 : v.adicCompletion ℚ ⊗[ℚ] L) := by
    rw [SubmonoidClass.coe_pow]
    show ((π : v.adicCompletion ℚ) • (1 : v.adicCompletion ℚ ⊗[ℚ] L)) ^ n = _
    rw [smul_pow, one_pow]
  have hv : Valued.v ((π : v.adicCompletion ℚ) ^ n) = exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  constructor
  · rintro ⟨y, rfl⟩ i
    rw [Subring.coe_mul, hc, mul_smul_comm, mul_one, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hv]
    exact mul_le_of_le_one_right' ((mem_adicCompletionIntegers _ _ _).1 (y.2 i))
  · intro hx
    have hπ0 : (π : v.adicCompletion ℚ) ^ n ≠ 0 := by
      intro h; rw [h, map_zero] at hv; exact exp_ne_zero hv.symm
    refine ⟨⟨((π : v.adicCompletion ℚ) ^ n)⁻¹ • (x : v.adicCompletion ℚ ⊗[ℚ] L), fun i => ?_⟩, Subtype.ext ?_⟩
    · rw [mem_adicCompletionIntegers, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_inv₀, hv]
      calc (exp (-(n : ℤ)))⁻¹ * Valued.v _ ≤ (exp (-(n : ℤ)))⁻¹ * exp (-(n : ℤ)) :=
            by gcongr; exact hx i
        _ = 1 := inv_mul_cancel₀ exp_ne_zero
    · rw [Subring.coe_mul, hc, mul_smul_comm, mul_one, smul_smul, mul_inv_cancel₀ hπ0, one_smul]

theorem small_iff (x : lam v bL h1 hmul) :
    IsSmallB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L) ↔ x ∈ Ideal.span {unif v bL h1 hmul π} := by
  have := mem_pow_iff v bL h1 hmul π hπ x 1
  rw [pow_one, smul_eq_mul, Ideal.mul_top] at this
  rw [this]
  simp only [Nat.cast_one]
  exact forall_congr' fun i => Formalism.BasicNotions.Examples₂.wz_lt_one_iff _

theorem isAdicComplete :
    IsAdicComplete (Ideal.span {unif v bL h1 hmul π}) (lam v bL h1 hmul) := by
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have key := mem_pow_iff v bL h1 hmul π hπ
  haveI hO := Formalism.BasicNotions.Examples₂.adicInt_isAdicComplete (K := ℚ) v
  set e := Algebra.TensorProduct.basis (v.adicCompletion ℚ) bL with he
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  · suffices h : (x : v.adicCompletion ℚ ⊗[ℚ] L) = 0 from Subtype.ext h
    apply e.repr.injective
    refine Finsupp.ext fun i => ?_
    rw [map_zero, Finsupp.zero_apply]
    refine Formalism.BasicNotions.Examples₂.adicInt_eq_zero_of_forall (K := ℚ) v _ fun n => ?_
    have := (key x n).1 (by simpa using (SModEq.sub_mem.1 (hx n)))
    exact this i
  · have hcoord : ∀ i, ∃ Li : v.adicCompletionIntegers ℚ, ∀ n,
        Valued.v (e.repr (f n : v.adicCompletion ℚ ⊗[ℚ] L) i - Li) ≤ exp (-(n : ℤ)) := by
      intro i
      obtain ⟨Li, hLi⟩ := IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ))
        (fun n => (⟨e.repr (f n : v.adicCompletion ℚ ⊗[ℚ] L) i, (f n).2 i⟩ : v.adicCompletionIntegers ℚ))
        (fun {m n} hmn => by
          rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Formalism.BasicNotions.Examples₂.adicInt_mem_pow_iff]
          have := (key (f m - f n) m).1 (SModEq.sub_mem.1 (hf hmn)) i
          simpa [map_sub] using this)
      refine ⟨Li, fun n => ?_⟩
      have := SModEq.sub_mem.1 (hLi n)
      rw [smul_eq_mul, Ideal.mul_top, Formalism.BasicNotions.Examples₂.adicInt_mem_pow_iff] at this
      simpa using this
    choose Lc hLc using hcoord
    have hrep : ∀ (w : κ → v.adicCompletion ℚ) i, e.repr (e.equivFun.symm w) i = w i := fun w i => by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hLmem : IsIntB v bL (e.equivFun.symm fun i => (Lc i : v.adicCompletion ℚ)) := fun i => by
      rw [hrep]; exact (Lc i).2
    refine ⟨⟨_, hLmem⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, key]
    intro i
    have h := hLc i n
    rw [AddSubgroupClass.coe_sub, map_sub, Finsupp.sub_apply]
    rw [show (e.repr ((⟨_, hLmem⟩ : lam v bL h1 hmul) : v.adicCompletion ℚ ⊗[ℚ] L)) i = (Lc i : v.adicCompletion ℚ) from hrep _ i]
    simpa using h

end GlobalTheory.AdicSpan.HenselSqrt

namespace GlobalTheory.AdicSpan.HenselSqrt

open IsDedekindDomain.HeightOneSpectrum WithZero

theorem exists_sqrt : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (κ : Type)
    (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    ∀ u : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL u → IsSmallB v bL (u - 1) →
    ∃ f : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑f ∧ IsIntB v bL ↑f⁻¹ ∧
      (f : v.adicCompletion ℚ ⊗[ℚ] L) ^ 2 = u ∧
      IsSmallB v bL (↑f - 1) ∧
      ∀ g : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL g → g ^ 2 = u → IsSmallB v bL (g - 1) → g = ↑f := by
  intro v L _ _ κ bL h2 h1 hmul _ u hu hsu
  obtain ⟨π, hπ⟩ := Formalism.BasicNotions.Examples₂.adicInt_exists_unif (K := ℚ) v
  haveI := isAdicComplete v bL h1 hmul π hπ
  haveI : HenselianRing (lam v bL h1 hmul) (Ideal.span {unif v bL h1 hmul π}) :=
    IsAdicComplete.henselianRing _ _
  have hI := small_iff v bL h1 hmul π hπ
  have hjac : ∀ x ∈ Ideal.span {unif v bL h1 hmul π}, IsUnit (x + 1) := fun x hx => by
    simpa using Ring.mem_jacobson_iff.1 (HenselianRing.jac hx) 1

  have h20 : (2 : v.adicCompletion ℚ) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
  have h2O : (2 : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    rw [mem_adicCompletionIntegers, map_inv₀, h2, inv_one]
  let t : lam v bL h1 hmul := ⟨(2 : v.adicCompletion ℚ)⁻¹ • 1, isIntB_smul v bL h2O h1⟩
  have ht : (2 : lam v bL h1 hmul) * t = 1 := by
    apply Subtype.ext
    show (2 : v.adicCompletion ℚ ⊗[ℚ] L) * ((2 : v.adicCompletion ℚ)⁻¹ • 1) = 1
    rw [mul_smul_comm, mul_one,
      show (2 : v.adicCompletion ℚ ⊗[ℚ] L) = (2 : v.adicCompletion ℚ) • (1 : v.adicCompletion ℚ ⊗[ℚ] L) by
        rw [two_smul, one_add_one_eq_two],
      smul_smul, inv_mul_cancel₀ h20, one_smul]
  have h2u : IsUnit (2 : lam v bL h1 hmul) := ⟨⟨2, t, ht, by rw [mul_comm]; exact ht⟩, rfl⟩

  let u' : lam v bL h1 hmul := ⟨u, hu⟩
  obtain ⟨a, ha, haI⟩ := HenselianRing.is_henselian (I := Ideal.span {unif v bL h1 hmul π})
    (Polynomial.X ^ 2 - Polynomial.C u') (Polynomial.monic_X_pow_sub_C _ two_ne_zero) 1 (by
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow,
        ← hI]
      have := isSmallB_neg v bL hsu
      rwa [neg_sub] at this) (by
      have : Polynomial.eval 1 (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C u')) = 2 := by
        set_option synthInstance.maxHeartbeats 200000 in
          simp; try norm_num
      rw [this]; exact h2u.map _)
  have ha2 : a ^ 2 = u' := by
    have := ha.eq_zero
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at this
    exact sub_eq_zero.1 this
  have haU : IsUnit a := by
    have := hjac _ haI
    rwa [sub_add_cancel] at this
  refine ⟨Units.map (lam v bL h1 hmul).subtype.toMonoidHom haU.unit, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Units.coe_map, IsUnit.unit_spec]; exact a.2
  · rw [← map_inv]; simp only [Units.coe_map]; exact (haU.unit⁻¹ : (lam v bL h1 hmul)ˣ).1.2
  · simp only [Units.coe_map, IsUnit.unit_spec]
    exact congrArg Subtype.val ha2
  · simp only [Units.coe_map, IsUnit.unit_spec]
    exact (hI (a - 1)).2 haI
  · intro g hg hg2 hgs
    simp only [Units.coe_map, IsUnit.unit_spec]
    let g' : lam v bL h1 hmul := ⟨g, hg⟩
    have hgI : g' - 1 ∈ Ideal.span {unif v bL h1 hmul π} := (hI (g' - 1)).1 hgs
    have hg'2 : g' ^ 2 = u' := Subtype.ext hg2
    have h0 : (g' - a) * (g' + a) = 0 := by
      have : (g' - a) * (g' + a) = g' ^ 2 - a ^ 2 := by ring
      rw [this, hg'2, ha2, sub_self]
    have hx := hjac _ (Ideal.mul_mem_right t _ (add_mem hgI haI))
    have hsum : g' + a = 2 * (((g' - 1) + (a - 1)) * t + 1) := by
      linear_combination (-(g' + a - 2)) * ht
    have hU : IsUnit (g' + a) := by rw [hsum]; exact h2u.mul hx
    have := (hU.mul_left_eq_zero).1 h0
    exact congrArg Subtype.val (sub_eq_zero.1 this)

end GlobalTheory.AdicSpan.HenselSqrt
end
end

