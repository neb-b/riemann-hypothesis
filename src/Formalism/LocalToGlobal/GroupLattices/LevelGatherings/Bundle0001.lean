module

public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.HostPlacesWeight
public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelGatherings.CastGLApply
section
noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.G Formalism.UG NumberField IsDedekindDomain
open scoped TensorProduct

def castGL {a b : ℕ} (h : a = b) (R : Type) [CommRing R] : GL (Fin a) R ≃* GL (Fin b) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv ℕ R (finCongr h)).toMulEquiv

theorem castGL_apply {a b : ℕ} (h : a = b) (R : Type) [CommRing R] (g : GL (Fin a) R) (x y : Fin b) :
    (castGL h R g : Matrix (Fin b) (Fin b) R) x y = (g : Matrix (Fin a) (Fin a) R) (Fin.cast h.symm x) (Fin.cast h.symm y) := by
  first
  | rfl
  | simp [castGL, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
  (σE : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E)
  (Up : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))

abbrev compC : Type :=
  ClassSet ((ratPts σE J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σE J (FiniteAdeleRing (𝓞 F) F)))
    (Up.subgroupOf (UPts σE J (FiniteAdeleRing (𝓞 F) F)))

def gamC (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Subgroup (UJ (σE : E →+* E) J) :=
  ((Up.map (MulAut.conj y).toMonoidHom).comap
    (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)))).subgroupOf (UJ (σE : E →+* E) J)

def gamMat (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : gamC σE J Up y →* GL (Fin k) E :=
  (UJ (σE : E →+* E) J).subtype.comp (gamC σE J Up y).subtype

def gamToUp (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : gamC σE J Up y →* Up :=
  ((MulAut.conj y⁻¹).toMonoidHom.comp
    ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).comp (gamMat σE J Up y))).codRestrict Up (by
      intro γ
      have h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gamMat σE J Up y γ) ∈
          Up.map (MulAut.conj y).toMonoidHom := γ.2
      obtain ⟨u, hu, hγ⟩ := h
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hγ ⊢
      rw [← hγ]
      simpa [mul_assoc] using hu)

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

abbrev levC (hS : HidaSetting p n' W Qq O Kf ι σ j w) (nV r : ℕ) (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ)
    (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = k) (iw : Fin nV → (E →+* Qq)) (fr : Fin nV → GL (Fin k) Qq) (ψ : Up →* Oˣ)
    (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Level (placesConst hS nV m r lam0 dom) where
  Γ := gamC σE J Up y
  act := fun v => (castGL hk Qq).symm.toMonoidHom.comp
    ((MulAut.conj (fr v)⁻¹).toMonoidHom.comp ((bc (iw v)).comp (gamMat σE J Up y)))
  χ := ψ.comp (gamToUp σE J Up y)

theorem levC_act (hS : HidaSetting p n' W Qq O Kf ι σ j w) (nV r : ℕ) (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ)
    (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = k) (iw : Fin nV → (E →+* Qq)) (fr : Fin nV → GL (Fin k) Qq) (ψ : Up →* Oˣ)
    (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : Fin nV) (γ : gamC σE J Up y) :
    castGL hk Qq ((levC σE J Up hS nV r lam0 dom hk iw fr ψ y).act v γ) =
      (fr v)⁻¹ * bc (iw v) (gamMat σE J Up y γ) * fr v := by

  change castGL hk Qq ((castGL hk Qq).symm ((fr v)⁻¹ * bc (iw v) (gamMat σE J Up y γ) * (fr v)⁻¹⁻¹)) = _
  rw [MulEquiv.apply_symm_apply, inv_inv]

abbrev gatConst (hS : HidaSetting p n' W Qq O Kf ι σ j w) (nV r : ℕ) (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ)
    (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = k) (iw : Fin nV → (E →+* Qq)) (fr : Fin nV → GL (Fin k) Qq) (ψ : Up →* Oˣ)
    (y : compC σE J Up → GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) [Finite (compC σE J Up)] (e : ℕ) : GAtP p where
  O := O
  Kf := Kf
  P := placesConst hS nV m r lam0 dom
  comp := compC σE J Up
  finComp := Fintype.ofFinite _
  lev := fun i => levC σE J Up hS nV r lam0 dom hk iw fr ψ (y i)
  e := e

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelGatherings.StdSubPlacesConst
section
noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.G

variable {p n' : ℕ} {W Qq Os Ks O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing Os] [IsDomain Os] [IsDiscreteValuationRing Os] [Field Ks] [Algebra Os Ks]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ιs : Qq →+* Ks} {σ : Qq ≃+* Qq} {js : W →+* Os} {ws : Os}

structure ExtOf (Os Ks O Kf : Type) [CommRing Os] [Field Ks] [Algebra Os Ks] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] where
  φ : Os →+* O
  φK : Ks →+* Kf
  comm : ∀ x : Os, φK (algebraMap Os Ks x) = algebraMap O Kf (φ x)
  fin : φ.Finite
  frac : IsFractionRing O Kf
  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O

theorem setting_ext (h : UnramifiedQuadraticSetting p n' W Qq Os Ks ιs σ js ws) (X : ExtOf Os Ks O Kf) :
    HidaSetting p n' W Qq O Kf (X.φK.comp ιs) σ (X.φ.comp js) (X.φ ws) := by
  exact
    { prime := h.1.prime
      five_le := h.1.five_le
      two_le := h.1.two_le
      even := h.1.even
      frac_alt := h.1.frac_alt
      frac_O := X.frac
      p_unif := h.1.p_unif
      res_card := h.1.res_card
      eq_sum_herm_smul_frame_of_inW := h.1.eq_sum_herm_smul_frame_of_inW
      frob := h.1.frob
      period := h.1.period
      ι_comp := by
        intro x
        simp only [RingHom.comp_apply]
        rw [h.1.ι_comp, X.comm]
      finite := X.fin.comp h.1.finite
      complete_O := X.complete
      w_sq := by rw [← map_pow, h.1.w_sq, map_natCast] }

end Formalism.L2.G
end
end

