module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabilisesCompletedLatticeIffLocalMatrixIntegral
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp.StabLoc

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (O : Subring R)

theorem mem_range_iff (m : GL n R) :
    m ∈ (Formalism.UG.bc (n := n) O.subtype).range ↔
      ∀ y : n → R, (∀ i, y i ∈ O) ↔ ∀ i, m.1.mulVec y i ∈ O := by
  have key : ∀ (A : Matrix n n R), (∀ i j, A i j ∈ O) → ∀ y : n → R, (∀ i, y i ∈ O) →
      ∀ i, A.mulVec y i ∈ O := fun A hA y hy i =>
    O.sum_mem fun j _ => O.mul_mem (hA i j) (hy j)
  have hs : ∀ j i : n, (Pi.single j (1 : R) : n → R) i ∈ O := by
    intro j i
    by_cases h : i = j
    · subst h; simp [O.one_mem]
    · simp [h, O.zero_mem]
  constructor
  · rintro ⟨k, rfl⟩ y
    refine ⟨key _ (fun i j => (k.1 i j).2) y, fun h => ?_⟩
    have := key (Formalism.UG.bc (n := n) O.subtype k⁻¹).1 (fun i j => ((k⁻¹).1 i j).2) _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at this
  · intro h
    have h1 : ∀ i j, m.1 i j ∈ O := fun i j => by
      simpa using (h (Pi.single j 1)).1 (hs j) i
    have h2 : ∀ i j, (m⁻¹).1 i j ∈ O := fun i j => by
      have := (h ((m⁻¹).1.mulVec (Pi.single j 1))).2 (by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        exact hs j) i
      rwa [Matrix.mulVec_single_one] at this
    let A : Matrix n n O := Matrix.of fun i j => ⟨m.1 i j, h1 i j⟩
    let B : Matrix n n O := Matrix.of fun i j => ⟨(m⁻¹).1 i j, h2 i j⟩
    have hA : O.subtype.mapMatrix A = m.1 := rfl
    have hB : O.subtype.mapMatrix B = (m⁻¹).1 := rfl
    have hinj : Function.Injective (O.subtype.mapMatrix : Matrix n n O →+* Matrix n n R) :=
      fun X Y hXY => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hXY i) j)
    refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    · rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]

end Ring

theorem stab_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E))
    (hh : IsFrameAt V v h) (g : HA (AF F) hc.sig V.gram) (hg : ∀ w, w ≠ v → locMat hc V w g = 1) :
    Stab hc V g ↔
      h⁻¹ * locMat hc V v g * h ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range := by
  have hev : ∀ w (y : Fin V.rank → Af F ⊗[F] E),
      (fun i => evF E w ((finMat hc.sig V.gram g).mulVec y i)) =
        (locMat hc V w g).1.mulVec fun i => evF E w (y i) := fun w y => by
    funext i
    rw [locMat_val]
    exact RingHom.map_mulVec (evF E w) _ y i
  have hloc : Stab hc V g ↔ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔
      (locMat hc V v g).1.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
    constructor
    · intro hs x
      have hx : ∀ w, w ≠ v → (fun i => evF E w (sgT E v (x i))) = 0 := fun w hw =>
        funext fun i => evF_sgT_ne hw _
      have hxv : (fun i => evF E v (sgT E v (x i))) = x := funext fun i => evF_sgT_self v _
      have := hs fun i => sgT E v (x i)
      rw [mem_lamHat_iff, mem_lamHat_iff] at this
      simp only [hev] at this
      constructor
      · intro h0
        have h1 := this.1 (fun w => by
          by_cases hw : w = v
          · subst hw; rw [hxv]; exact h0
          · rw [hx w hw]; exact zero_mem _) v
        rwa [hxv] at h1
      · intro h0
        have h1 := this.2 (fun w => by
          by_cases hw : w = v
          · subst hw; rw [hxv]; exact h0
          · rw [hx w hw, Matrix.mulVec_zero]; exact zero_mem _) v
        rwa [hxv] at h1
    · intro hs y
      rw [mem_lamHat_iff, mem_lamHat_iff]
      refine forall_congr' fun w => ?_
      rw [hev]
      by_cases hw : w = v
      · subst hw; exact hs _
      · rw [hg w hw, Units.val_one, Matrix.one_mulVec]
  rw [hloc, mem_range_iff]
  constructor
  · intro hs y
    have := hs (h.1.mulVec y)
    rw [hh, hh, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rwa [Units.val_mul, Units.val_mul]
  · intro hs x
    have := hs ((h⁻¹).1.mulVec x)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, Units.val_mul,
      ← Matrix.mulVec_mulVec] at this
    rw [hh, hh]
    exact this

end GlobalTheory.PlaceComp.StabLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterMonodromyZeroOfUnramified
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

namespace GlobalTheory.TameType

theorem irreducible_twist {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
    (h : ρ.IsIrreducible) (ν : Γ →* ℂˣ) : (twist ρ ν).IsIrreducible := by
  let f : Subrepresentation (twist ρ ν) → Subrepresentation ρ := fun S =>
    ⟨S.toSubmodule, fun g v hv => by
      have h1 := S.toSubmodule.smul_mem ((ν g)⁻¹ : ℂˣ).1 (S.apply_mem_toSubmodule g hv)
      simpa [smul_smul] using h1⟩
  have hn : (⊥ : Submodule ℂ V) ≠ ⊤ := fun e =>
    (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
  have : Nontrivial (Subrepresentation (twist ρ ν)) := ⟨⊥, ⊤, fun e =>
    hn (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top (f S) with e | e
  · exact Or.inl (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))
  · exact Or.inr (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))

theorem charpoly_scalar {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (z : ℂ) :
    (z • (1 : Module.End ℂ V)).charpoly = (X - C z) ^ Module.finrank ℂ V := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, LinearMap.toMatrix_one,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

section WD

open GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem weilDeligneParameter_monodromy_zero_of_unramified {a : WD h} (ha : a.unr) : a.mono0 := by
  induction a using WD.ind
  exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 ((WD.unr_mk _).1 ha).1

theorem inePol_of_unr {a : WD h} (ha : a.unr) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) :
    a.inePol σ = (X - 1) ^ a.lpDim := by
  induction a using WD.ind
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, ((WD.unr_mk _).1 ha).2, WD.lpDim_mk, LinearMap.charpoly_one]

theorem inePol_char_of_unr {a c : WD h} (ha : a.unr) (hc : c.lpDim = 1) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B)
    {z : ℂ} (hz : c.inePol σ = X - C z) : (a.lpChar c).inePol σ = (X - C z) ^ a.lpDim := by
  rw [← WD.lpDim_char a c hc]
  induction a using WD.ind with
  | hP m a =>
  induction c using WD.ind with
  | hP n c =>
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk] at hz
    have h1 := LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))
    rw [hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h1
    rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk, WDRep.tensor_ρ,
      ((WD.unr_mk _).1 ha).2, h1, TensorProduct.map_smul_right, TensorProduct.map_one, charpoly_scalar]

end WD

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem inertialType_of_tame :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
      (T : RowTie.WDTie N A) (S : SplitRead.Reading T) (i : N.Loc) (w : PlE H)
      (hw : IsSplitPl H w),
      TameSplitAll H.E → SplitRead.Laws S → SplitRead.TypeTame S i w hw →
      (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
        A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) →
      ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧
        ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
          A.inePol (A.locV i P w) σ =
            (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hTS hL hT hmu P
  obtain ⟨htame, hram, hv⟩ := hT
  obtain ⟨v, hv0, hv⟩ := hv P
  have L := hL i w hw
  have hs := (S i w hw).mu_ok.1
  obtain ⟨π₁, π₂, h1, h2, he⟩ := hTS w _ _ _ _ v hs htame hram hv0 hv
  let c : Irr (w.adicCompletion H.E) 1 :=
    { V := ℂ, π := detRep (Fin 1) (S i w hw).mu, smooth := (isSmooth_ofChar_iff _).2 hs.detChar,
      irr := isIrreducible_ofChar _ }
  let τ : Irr (w.adicCompletion H.E) R.t :=
    { V := π₂.V, π := twist π₂.π (detChar (Fin R.t) (S i w hw).mu), smooth := isSmooth_twist π₂.smooth hs.detChar,
      irr := irreducible_twist π₂.irr _ }
  have hc : Nonempty (c.π.Equiv (detRep (Fin 1) (S i w hw).mu)) := ⟨Representation.Equiv.refl _⟩
  have e1 := L.prod _ _ π₁ τ _ he
  have e2 := L.twist _ _ c π₂ τ hc ⟨Representation.Equiv.refl _⟩
  have u1 := (L.sph _ π₁).2 h1
  have u2 := (L.sph _ π₂).2 h2
  have eV := (S i w hw).locV P
  have eM := (S i w hw).locMu c hc
  rw [e1, e2] at eV
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [T.mono0, eV, WeilDeligne.WD.monomial_sum_iff, WeilDeligne.WD.monomial_char_iff _ _ (L.dim 1 c)]
    exact ⟨weilDeligneParameter_monodromy_zero_of_unramified u1, weilDeligneParameter_monodromy_zero_of_unramified u2⟩
  · have hz := hmu σ hσ
    rw [T.inePol _ _ _ hσ, eM] at hz
    rw [T.inePol _ _ _ hσ, eV, WeilDeligne.WD.inePol_sum, inePol_of_unr u1 hσ,
      inePol_char_of_unr u2 (L.dim 1 c) hσ hz, L.dim, L.dim]

end GlobalTheory.TameType
end
end

