module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1135
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLocalDualityOfLocalTateDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildInertiaKilledByAdditiveLocallyConstant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0686
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep
open scoped ContDiff

namespace GlobalTheory.SchurExt

def idemHom {R : Type} [CommRing R] (e : R) (he : IsIdempotentElem e) : R →ₙ+* R where
  toFun x := e * x
  map_mul' x y := by
    change e * (x * y) = e * x * (e * y)
    calc e * (x * y) = (e * e) * (x * y) := by rw [he.eq]
      _ = e * x * (e * y) := by ring
  map_zero' := mul_zero e
  map_add' x y := mul_add e x y

variable {E : Type} [Field E] [NumberField E]


open Classical in
def idemSf (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E :=
  ⟨fun w => if w ∈ S then 1 else 0, Filter.Eventually.of_forall fun w => by
    by_cases h : w ∈ S
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

theorem isIdempotentElem_idemSf (S : Finset (HeightOneSpectrum (𝓞 E))) : IsIdempotentElem (idemSf S) := by
  classical
  refine Subtype.ext (funext fun w => ?_)
  change (if w ∈ S then (1 : w.adicCompletion E) else 0) * (if w ∈ S then 1 else 0) = if w ∈ S then 1 else 0
  split_ifs <;> simp

def idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : Ad E := ((1 : InfiniteAdeleRing E), idemSf S)

theorem isIdempotentElem_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : IsIdempotentElem (idemS S) :=
  Prod.ext (mul_one _) (isIdempotentElem_idemSf S).eq

def prS (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GA E a →* GA E a :=
  cornerGL a (idemHom (idemS S) (isIdempotentElem_idemS S))

def prO (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GA E a →* GA E a :=
  cornerGL a (idemHom (1 - idemS S) (isIdempotentElem_idemS S).one_sub)

def prSf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GL (Fin a) (Af E) →* GL (Fin a) (Af E) :=
  cornerGL a (idemHom (idemSf S) (isIdempotentElem_idemSf S))

def prOf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GL (Fin a) (Af E) →* GL (Fin a) (Af E) :=
  cornerGL a (idemHom (1 - idemSf S) (isIdempotentElem_idemSf S).one_sub)

def eqv (m r : ℕ) : Fin (m + r + 1 + 1) ≃ Fin (m + 1) ⊕ Fin (r + 1) :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

section Blocks

variable {R : Type} [CommRing R] {m r : ℕ}

def blk (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R :=
  M.submatrix (eqv m r).symm (eqv m r).symm

def unblk (P : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R :=
  P.submatrix (eqv m r) (eqv m r)

def Aof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  (blk M).toBlocks₁₁

def Bof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (r + 1)) R :=
  (blk M).toBlocks₁₂

def Cof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (m + 1)) R :=
  (blk M).toBlocks₂₁

def Dof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  (blk M).toBlocks₂₂

def Xof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (r + 1)) R :=
  Bof M * (Dof M)⁻¹

def Yof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (m + 1)) R :=
  (Dof M)⁻¹ * Cof M

def Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Aof M - Bof M * (Dof M)⁻¹ * Cof M

theorem unblk_blk (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : unblk (blk M) = M := by
  ext i j; simp [unblk, blk]

theorem blk_unblk (P : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) : blk (unblk P) = P := by
  ext i j; simp [unblk, blk]

end Blocks


open Classical in
def mkGL {R : Type} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R) : GL (Fin k) R :=
  if h : IsUnit M.det then Matrix.nonsingInvUnit M h else 1

theorem coe_mkGL {R : Type} [CommRing R] {k : ℕ} {M : Matrix (Fin k) (Fin k) R} (h : IsUnit M.det) :
    ((mkGL M : GL (Fin k) R) : Matrix (Fin k) (Fin k) R) = M := by
  rw [mkGL, dite_eq_left h]; rfl

def psi (x : Ad E) : ℂ := (GroundTheory.Global.adelicChar E x : ℂ)

variable [_root_.NumberField.IsTotallyComplex E]

def chiF {m r : ℕ} (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) : ℂ :=
  open Classical in
  (χ (fun i j => pInf E (Y i j)) : ℂ) *
    (if ∀ i j, pFin E (Y i j) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E then 1 else 0)

def schurF {m r : ℕ} (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (g : GA E (m + r + 1 + 1)) : ℂ :=
  open Classical in
  if IsUnit (Dof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det then
    psi (Xof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0) *
      β (mkGL (Scof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))) *
      b₁ (mkGL (Dof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))) *
      chiF χ (Yof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))
  else 0

def extB {m r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ)
    (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ) (Φ : GA E (m + r + 1 + 1) → ℂ) (g : GA E (m + r + 1 + 1)) : ℂ :=
  schurF β b₁ χ (prS S _ g) * Φ (prO S _ g)

end GlobalTheory.SchurExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityClassFieldFactsOfArtinTateEuler
section
namespace GlobalTheory

theorem langRecCore_of_artinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hT : Formalism.GaloisCohomology.LocalTateDualityK)
    (hE : Formalism.GaloisCohomology.LocalEulerCharK) : ReciprocityTheory.ChartRestriction.T2.Core :=
  { dec := _root_.GlobalTheory.DecLocal.decEquiv,
    inv := GlobalTheory.T.invIso_of_localTateDuality hT,
    fin := GlobalTheory.T.finIso_dualLattice_of_localTateDuality hT,
    rat := _root_.GlobalTheory.ratIso_of_localTateDuality hT,
    int := GlobalTheory.T.integral_localDuality_of_localTateDuality hT,
    jspan := _root_.GlobalTheory.jSpan_holds,
    nat := GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist hT,
    shape := GlobalTheory.T.cohomology_shape_of_tate_duality_euler hT hE,
    shapeUnr := GlobalTheory.T.galoisHom_modulo_unramified_shape_of_localDuality hT hE,
    unr := _root_.GlobalTheory.UnrChar.unrDec,
    vhE := GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity hA,
    top := _root_.GlobalTheory.PadicTop.topEx,
    elem := _root_.GlobalTheory.LocElem.elem }

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAtTypes
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.WildSetSQ

theorem char_eq_one_of_wild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (had : IsAdic (IsLocalRing.maximalIdeal O)) (χ : G E Ω →* Oˣ)
    (hχ : Continuous fun g => ((χ g : Oˣ) : O)) (σ : G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1)
    (h : χ σ ^ m = 1) : χ σ = 1 := by
  have key : ∀ M : ℕ, ((χ σ : Oˣ) : O) - 1 ∈ IsLocalRing.maximalIdeal O ^ M := by
    intro M
    let H : Subgroup (G E Ω) :=
      ((Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ M)).toMonoidHom).comp χ).ker
    have hH : ∀ g, g ∈ H ↔ ((χ g : Oˣ) : O) - 1 ∈ IsLocalRing.maximalIdeal O ^ M := by
      intro g
      rw [← Ideal.Quotient.eq, map_one, MonoidHom.mem_ker, Units.ext_iff]
      rfl
    have ho : IsOpen (H : Set (G E Ω)) := by
      have e : (H : Set (G E Ω)) = (fun g => ((χ g : Oˣ) : O) - 1) ⁻¹'
          ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O) := by
        ext g
        exact hH g
      rw [e]
      exact ((isAdic_iff.1 had).1 M).preimage (hχ.sub continuous_const)
    refine (hH σ).1 (GlobalTheory.WildKill.mem_of_wild A H ho σ m hm hσ ?_)
    rw [hH, map_pow, h, Units.val_one, sub_self]
    exact zero_mem _
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero]
  have h2 := Ideal.mem_iInf.2 key
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at h2
  simpa using h2

theorem coprime_pred (g : ℕ) (hg : 1 ≤ g) : (g - 1).Coprime g := by
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  simp

end GlobalTheory.WildSetSQ

namespace GlobalTheory.WildSetSQ

end GlobalTheory.WildSetSQ

namespace GlobalTheory.WildSetSQ

end GlobalTheory.WildSetSQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxCompactUnitaryConjRelIndexEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

open GlobalTheory.UnimodMass in
theorem GlobalTheory.UnimodMass.umax_relIndex_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n), ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) ≠ 0 ∧ ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) = (Umax L n).relIndex ((Umax L n).map (MulAut.conj h).toMonoidHom) := by
  intro L _ _ _ n h
  set U := Umax L n with hUdef
  set V := U.map (MulAut.conj h).toMonoidHom with hVdef
  haveI hW : Finite (DC (GQ L n) (U ⊓ V)) := finite_dc_of_cover (_root_.GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj L n h)
  have hb : IsBounded U := ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using hκ⟩⟩
  have hU : ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ U} := fun t => _root_.GlobalTheory.StabFin.finite_conj_mem L n U hb t
  have hV : ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ V} := by
    intro t
    haveI := hU (t * h)
    refine Finite.of_injective (fun x : {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ V} =>
      (⟨x.1, ?_⟩ : {γ : GQ L n // (t * h)⁻¹ * (γ : GAf L n) * (t * h) ∈ U})) ?_
    · have hx : t⁻¹ * ((x.1 : GQ L n) : GAf L n) * t ∈ U.map (MulAut.conj h).toMonoidHom := x.2
      rw [Subgroup.mem_map_equiv] at hx
      simpa [MulAut.conj_symm_apply, mul_assoc] using hx
    · intro a b hab
      exact Subtype.ext (by simpa using congrArg Subtype.val hab)
  obtain ⟨h1, e1⟩ := GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass (GAf L n) (GQ L n) (U ⊓ V) U inf_le_left hW hU
  obtain ⟨h2, e2⟩ := GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass (GAf L n) (GQ L n) (U ⊓ V) V inf_le_right hW hV
  have e3 : mass (GQ L n) V = mass (GQ L n) U := mass_conj (GQ L n) U h
  haveI : Finite (DC (GQ L n) U) := finite_dc_of_le (Γ := GQ L n) (W := U ⊓ V) inf_le_left
  have hpos := mass_pos (Γ := GQ L n) (K := U) hU
  rw [Subgroup.inf_relIndex_left] at h1 e1
  rw [Subgroup.inf_relIndex_right] at h2 e2
  refine ⟨h1, ?_⟩
  rw [e3] at e2
  have : (V.relIndex U : ℚ) = (U.relIndex V : ℚ) := mul_right_cancel₀ hpos.ne' (e1.symm.trans e2)
  exact_mod_cast this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBoundOfComponents
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel.OddBound

theorem dec_le_of_frob_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {σ : G F Ω}
    (hσ : IsFrob A (normV v) σ) {L : Subgroup (G F Ω)} (hL : IsOpen (L : Set (G F Ω))) (hI : Ine (F := F) A ≤ L)
    (hm : σ ∈ L) : Dec (F := F) A ≤ L := by
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((L.subgroupOf (Dec (F := F) A) : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) :=
    (L.isClosed_of_isOpen hL).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) A) ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A))
    (sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_subgroupOf.2 hm)) (fun x hx => hI hx)) hc
  rw [h] at h2
  intro g hg
  exact h2 (Subgroup.mem_top (⟨g, hg⟩ : Dec (F := F) A))

theorem residual_bound_of_parts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ i, StepAB X i) → (∀ i, ChooseH bkP i) → (∀ i s, GalHyp bkP i s → ResBound bkP i s) → ResidualBoundOddPrimes bkP := by
  intro D N X bkP hAB hCh hRB i hl T hT
  obtain ⟨R, hR⟩ := hCh i T hT
  refine ⟨R, 4 * D.R.r * R, 4 * D.R.r * R + 2, fun M hM H S d hd z hz H' ho hn A => ?_⟩
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hlt : 4 * D.R.r * R + 2 < X.l i ^ M := lt_of_le_of_lt hM (Nat.lt_pow_self hp.one_lt)
  obtain ⟨L, hLo, hLn, hLH, hLs, hLζ, -⟩ := GlobalTheory.T.exists_open_normal_subgroup_under_inertia D N X bkP i T hT z hz M H hd.1 hd.2.1 hd.2.2.1
  obtain ⟨h, U, hh, hUo, hUn, hUL, hco⟩ := hR z hz L hLo hLn hLs
  obtain ⟨P, hAux, hSt, hIne, hFr⟩ := hAB i M (by omega) H S d hd z hz (U ⊓ H') (hUo.inter ho) inferInstance A R h
    (fun a => ⟨hLH (hh a), hLζ _ (hh a)⟩)
  choose φ g hφ hg using hFr
  have mono : ∀ V : Subgroup (GE N), U ⊓ H' ≤ V → Steps X i M V z P (fun q => d (P q)) := fun V hV =>
    ⟨fun a σ hσ => (hSt.1 a σ hσ).imp fun _ hg => hV hg, hSt.2⟩
  have hUL' : U ⊓ H' ≤ L := inf_le_left.trans hUL
  refine ⟨P, hAux, mono H' inf_le_right, fun s hs Q hQ a Φ hΦ F hF => ?_⟩
  have hφL : ∀ a, φ a ∈ L := fun a => by
    have h1 := L.mul_mem (hUL' (hg a)) (hh a)
    rw [inv_mul_cancel_right] at h1
    simpa [mul_assoc] using hLn.conj_mem _ h1 (g a)⁻¹
  have hcj : ∀ a, IsCj X (φ a) (GlobalTheory.TwistDet.cConj X (φ a)) := fun a x => rfl
  have hPos : Position i s M P (fun q => d (P q)) φ (fun a => GlobalTheory.TwistDet.cConj X (φ a)) := by
    refine ⟨⟨fun q v hv => ?_, hAux.2⟩, ⟨z, L, hz, hLs s hs, mono L hUL'⟩, fun a => ⟨fun k hk => ?_, hφ a, hcj a⟩⟩
    · obtain ⟨h1, h2, h3, h4, -, h6⟩ := hAux.1 q v hv
      exact ⟨h1, h2, h3, h4, Finset.notMem_empty _, h6⟩
    · exact (hLs s hs).2.2.2.2 k (dec_le_of_frob_mem (N.plOm.2 _) (hφ a) hLo
        ((hIne _ _ (Or.inl rfl) _ (N.plOm.2 _)).trans hUL') (hφL a) hk)
  have hc := hco φ (fun a => GlobalTheory.TwistDet.cConj X (φ a)) (fun a => ⟨hcj a, g a, (hg a).1⟩) s hs
  rw [if_pos hl] at hc
  obtain ⟨m, hm, hu⟩ := (hRB i s (hT s hs) M R P _ φ _ Q hlt hPos hQ a Φ hΦ).1 hc F hF
  exact ⟨m, hm, (IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu).le⟩

end GlobalTheory.ResSel.OddBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchwartzBruhatConjHalfLocallyConstantCompactSuppStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_conjHalf_locallyConstant_compactSupport : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latH S T ΛS ΛT) Φ → ∀ ϖ : (GlobalTheory.SplitHecke.Ov D v), Irreducible ϖ → ∃ N : ℕ, (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → ∀ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), rdAdj S T βS βT φ x' = rdAdj S T βS βT φ x + (ϖ ^ N • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) → Φ x' = Φ x) ∧ ∀ x : WO S T, Φ x ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) (ϖ ^ N) • rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
  intro D S T βS βT e PP v φ ι he hL ΛS ΛT hS hT Φ hΦ ϖ hϖ
  first
  | exact GlobalTheory.DownLift.SplitCoef.sbHalf_locConst_cptSupp D S T βS βT e PP v φ ι he hL ΛS ΛT hS hT Φ hΦ ϖ hϖ
  | exact GlobalTheory.DownLift.SplitCoef.sbHalf_locConst_cptSupp D S T βS βT e PP v φ ι he hL ΛS ΛT hS.toIsLattice hT.toIsLattice Φ hΦ ϖ hϖ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameRelationCocycleSquareZeroInertia
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.TameRelation

open GlobalTheory.TameQuot

theorem eq_one_of_index_coprime {J N : Type} [Group J] [AddCommGroup N] {l k : ℕ}
    (hN : ∀ m : N, (l ^ k) • m = 0) (θ : J →* Multiplicative N) (h : θ.ker.index.Coprime l)
    (σ : J) : θ σ = 1 := by
  have h1 : θ σ ^ θ.ker.index = 1 := by
    rw [← map_pow]; exact θ.ker.pow_index_mem σ
  have h2 : θ σ ^ l ^ k = 1 := hN (θ σ).toAdd
  exact (pow_eq_one_iff_of_coprime (h.pow_right k)).1 ⟨h1, h2⟩

theorem pow_formula {Γ R W : Type} [Group Γ] [CommRing R] [AddCommGroup W] [Module R W]
    (ρ : Representation R Γ W) {b : R} (hb : b * b = 0) {γ : Γ} (hγ : ∀ m, ρ γ m = m + b • m)
    (z : Γ → W) (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) (k : ℕ) :
    (∀ m, ρ (γ ^ k) m = m + k • b • m) ∧ z (γ ^ k) = k • z γ + k.choose 2 • b • z γ := by
  have hbb : ∀ m : W, b • b • m = 0 := fun m => by rw [← mul_smul, hb, zero_smul]
  induction k with
  | zero => simpa using hz 1 1
  | succ k ih =>
    refine ⟨fun m => ?_, ?_⟩
    · rw [pow_succ', map_mul, Module.End.mul_apply, ih.1, hγ, smul_add, smul_comm b k, hbb,
        smul_zero, add_zero, succ_nsmul]
      abel
    · rw [pow_succ', hz, ih.2, hγ, smul_add, smul_comm b k, smul_comm b (k.choose 2), hbb,
        smul_zero, add_zero, succ_nsmul, Nat.choose_succ_succ' k 1, Nat.choose_one_right, add_smul]
      abel

theorem tame_relation : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ (k : ℕ), normV v % (2 * l ^ k) = 1 → ∀ (M : ℕ) (d : G F Ω →* Multiplicative (ZMod (l ^ M))) (γ σ : G F Ω), 1 ≤ M → IsOpen (d.ker : Set (G F Ω)) → γ ∈ Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → IsFrob A (normV v) σ → ∀ (R : Type) [CommRing R] (W : Type) [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W] (ρ : Representation R (G F Ω) W) (a b : R), (∀ m : W, (l ^ k) • m = 0) → b * b = 0 → (∀ τ ∈ Ine (F := F) A, ∀ m, ρ τ m = m + (((Multiplicative.toAdd (d τ)).val : R) * b) • m) → (∀ m, ρ σ m = m + a • m) → ∀ z : Z1 ρ, a • z.1 γ = b • z.1 σ ∧ (b = 0 → z.1 γ = 0 → ∀ τ ∈ Ine (F := F) A, z.1 τ = 0) := by
  intro hT F Ω _ _ _ _ _ l hlp A v hA hl k hq M d γ σ hM hd hγ hdγ hσ R _ W _ _ _ _ ρ a b h4 hb hI hρ z
  obtain ⟨-, -, hco, ⟨t, tc, ts, hk⟩, -, -⟩ := hT F Ω l A v hA hl
  haveI : Fact (1 < l ^ M) := ⟨one_lt_pow₀ hlp.out.one_lt (by omega)⟩
  have hdJ : ∀ τ ∈ ineKer F A l, d τ = 1 := fun τ hτ =>
    eq_one_of_index_coprime (l := l) (k := M) (fun m => by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
      (d.comp (ineKer F A l).subtype) (hco _ inferInstance (hd.preimage continuous_subtype_val)) ⟨τ, hτ⟩
  have hρJ : ∀ τ ∈ ineKer F A l, ∀ m, ρ τ m = m := fun τ hτ m => by
    rw [hI τ (ineKer_le_Ine A l hτ), hdJ τ hτ]; simp
  have hzJ : ∀ τ ∈ ineKer F A l, z.1 τ = 0 := fun τ hτ => by
    let θ : ineKer F A l →* Multiplicative W :=
      MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
        have := z.2.2 (g : G F Ω) h
        rw [hρJ _ g.2] at this
        exact congrArg Multiplicative.ofAdd this
    have ho : IsOpen (θ.ker : Set (ineKer F A l)) :=
      (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
    exact eq_one_of_index_coprime (l := l) (k := k) h4 θ
      (hco _ inferInstance ho) ⟨τ, hτ⟩
  refine ⟨?_, fun hb0 h0 τ hτ => ?_⟩
  · have hj := tame_rel hA hl hσ hγ
    have hγ' : ∀ m, ρ γ m = m + b • m := fun m => by
      rw [hI γ hγ, hdγ, toAdd_ofAdd, ZMod.val_one, Nat.cast_one, one_mul]
    obtain ⟨p1, p2⟩ := pow_formula ρ hb hγ' z.1 z.2.2 (normV v)
    have hqs : ∀ m : W, normV v • m = m := KStar.Tree.nsmul_eq_self_of_mod hq h4
    obtain ⟨c, hc⟩ := KStar.Tree.dvd_choose_two hq
    rw [hc, mul_comm (l ^ k), mul_smul, h4, smul_zero, add_zero, hqs] at p2
    have e : σ * γ = γ ^ normV v * (((γ ^ normV v)⁻¹ * (σ * γ * σ⁻¹)) * σ) := by group
    have h1 := z.2.2 σ γ
    rw [e, z.2.2, z.2.2 _ σ, hzJ _ hj, hρJ _ hj, zero_add, p1, p2, hqs, hρ, ← add_assoc,
      ← add_assoc, add_comm (z.1 γ)] at h1
    exact (add_left_cancel h1).symm
  · have hg : IsProGen F A l γ := by
      refine (isProGen_iff_isUnit F Ω l A t tc ts hk ⟨γ, hγ⟩).2 ?_
      by_contra hu
      obtain ⟨y, hy⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.mem_nonunits.1 hu)
      obtain ⟨g, hg⟩ := ts (Multiplicative.ofAdd y)
      have h1 : t ((g ^ l)⁻¹ * ⟨γ, hγ⟩) = 1 := by
        rw [map_mul, map_inv, map_pow, inv_mul_eq_one, hg]
        refine Multiplicative.toAdd.injective ?_
        rw [hy, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul]
      have h2 : d (((g : G F Ω) ^ l)⁻¹ * γ) = 1 := hdJ _ ((hk _).1 h1)
      rw [map_mul, map_inv, map_pow, inv_mul_eq_one, hdγ] at h2
      have h3 := congrArg (fun x => ZMod.castHom (dvd_pow_self l (by omega : M ≠ 0)) (ZMod l)
        (Multiplicative.toAdd x)) h2
      simp only [toAdd_pow, toAdd_ofAdd, map_one, nsmul_eq_mul, map_mul, map_natCast,
        ZMod.natCast_self, zero_mul] at h3
      exact zero_ne_one h3
    let θ : Ine (F := F) A →* Multiplicative W :=
      MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
        have := z.2.2 (g : G F Ω) h
        rw [hI _ g.2, hb0, mul_zero, zero_smul, add_zero] at this
        exact congrArg Multiplicative.ofAdd this
    have ho : IsOpen (θ.ker : Set (Ine (F := F) A)) :=
      (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
    have hc : IsClosed ((θ.ker.map (Ine (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
      (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (θ.ker.isClosed_of_isOpen ho)
    have h1 : Subgroup.zpowers γ ⊔ ineKer F A l ≤ θ.ker.map (Ine (F := F) A).subtype :=
      sup_le (Subgroup.zpowers_le.2 ⟨⟨γ, hγ⟩, h0, rfl⟩) fun τ hτ =>
        ⟨⟨τ, ineKer_le_Ine A l hτ⟩, hzJ τ hτ, rfl⟩
    obtain ⟨τ', hτ', rfl⟩ := Subgroup.topologicalClosure_minimal _ h1 hc (hg.2 hτ)
    exact hτ'

end GlobalTheory.TameRelation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistFrontInputs
section
open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Published

namespace GlobalTheory

theorem twist_front_inputs : PoitouTateDuality → LocalFiniteness → LocalTateDuality → LocalFinitenessK → LocalTateDualityK → LocalEulerCharK → GlobalArtinReciprocity → GlobalTheory.TwSys.Cheb ∧ ChebotarevDegreeOne ∧ ChebotarevOpenNormal ∧ PoitouTateTotallyComplex ∧ CohDimTwo ∧ TameLocal ∧ Formalism.MainNotions.BlochKatoReduction.Gen.ArchimedeanSignatureMatching ∧ RayCharacterArtin :=
  fun hP hF hT a b c hA => ⟨cheb_holds, chebotarevDegreeOne', cheb_holds, hP.totallyComplex, ⟨hP.cohDimTwoGlobal, cohDimTwoLocal_of_localFiniteness hF⟩, TameLocal_of_duality hT, (GlobalTheory.TateLimit.twist_cohomology_inputs hP a b c).1, hA.rayCharacterArtin⟩

end GlobalTheory
end

