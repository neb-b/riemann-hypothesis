module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen
open scoped TensorProduct

namespace GlobalTheory.ExportCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section Index

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem sIdx_eq {W : Type} [AddCommGroup W] [Module R W] (l : ℕ) (M N : Submodule R W) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M N =
      (signedLength M N : ℝ) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) := by
  simp only [Formalism.MainNotions.IntegralHeckeForms.sIdx, Formalism.MainNotions.IntegralHeckeForms.lenR, signedLength, relLength_eq_length_quotient_comap]
  push_cast
  rw [sub_div]

theorem sIdx_map {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (f : W →ₗ[R] W') (hf : Function.Injective f) (l : ℕ) (M N : Submodule R W) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l (M.map f) (N.map f) = Formalism.MainNotions.IntegralHeckeForms.sIdx l M N := by
  simp only [sIdx_eq, signedLength, relLength_map_of_injective f hf]

variable {W : Type} [AddCommGroup W] [Module (FractionRing R) W] [Module R W]
  [IsScalarTower R (FractionRing R) W]

theorem isLatIn_iff (V : Submodule (FractionRing R) W) (L : Submodule R W) :
    ToricLatticeDenominators.IsLatIn V L ↔ Formalism.MainNotions.IntegralHeckeForms.IsLatIn L (V.restrictScalars R) := by
  refine and_congr_right fun _ => ⟨fun h => ⟨fun x hx => ?_, fun x hx => ?_⟩, fun h => ?_⟩
  · rw [← h]; exact Submodule.subset_span hx
  · rw [← h, Submodule.restrictScalars_mem] at hx
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) (FractionRing R)
      (L : Set W) x hx
    rw [Submodule.span_eq] at hc
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
  · refine le_antisymm (Submodule.span_le.2 h.1) fun x hx => ?_
    obtain ⟨c, hc, hx⟩ := h.2 x hx
    have hc' : algebraMap R (FractionRing R) c ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hc
    have : x = (algebraMap R (FractionRing R) c)⁻¹ • (c • x) := by
      rw [← algebraMap_smul (FractionRing R) c x, inv_smul_smul₀ hc']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

def inside (V : Submodule (FractionRing R) W) (L : Submodule R W) : Submodule R ↥V :=
  L.comap (V.subtype.restrictScalars R)

end Index

section Transport

theorem isLatIn_map_iff {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W']
    [Module R W'] (f : W →ₗ[R] W') (hf : Function.Injective f) (M V : Submodule R W) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (M.map f) (V.map f) ↔ Formalism.MainNotions.IntegralHeckeForms.IsLatIn M V := by
  refine ⟨fun h => ⟨Submodule.fg_of_fg_map_injective f hf h.1,
    (Submodule.map_le_map_iff_of_injective hf _ _).1 h.2.1, fun x hx => ?_⟩,
    fun h => ⟨h.1.map f, Submodule.map_mono h.2.1, ?_⟩⟩
  · obtain ⟨c, hc, y, hy, e⟩ := h.2.2 (f x) ⟨x, hx, rfl⟩
    rw [← map_smul] at e
    exact ⟨c, hc, hf e ▸ hy⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hy⟩ := h.2.2 x hx
    exact ⟨c, hc, c • x, hy, map_smul _ _ _⟩

theorem isLatIn_span {R S W W' : Type} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (hi : Function.Injective (algebraMap R S)) [AddCommGroup W] [Module R W] [AddCommGroup W']
    [Module R W'] [Module S W'] [IsScalarTower R S W'] (r : W →ₗ[R] W') {L V : Submodule R W}
    (h : Formalism.MainNotions.IntegralHeckeForms.IsLatIn L V) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Submodule.span S (r '' L)) (Submodule.span S (r '' V)) := by
  refine ⟨?_, Submodule.span_mono (Set.image_mono h.2.1), fun x hx => ?_⟩
  · obtain ⟨s, hs⟩ := h.1.map r
    rw [← Submodule.map_coe, ← hs, Submodule.span_span_of_tower]
    exact Submodule.fg_span s.finite_toSet
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨c, hc, hy⟩ := h.2.2 y hy
      refine ⟨algebraMap R S c, (map_ne_zero_iff _ hi).2 hc, Submodule.subset_span ⟨_, hy, ?_⟩⟩
      rw [map_smul, algebraMap_smul]
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨d, hd, hy⟩ := hy
      refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      exact ⟨c, hc, by rw [smul_comm]; exact Submodule.smul_mem _ _ hx⟩

variable (O : Type) [CommRing O] [IsDomain O] (F : Type) [AddCommGroup F]
  [Module (FractionRing O) F] [Module O F] [IsScalarTower O (FractionRing O) F]
  (O' : Type) [CommRing O'] [IsDomain O'] [Algebra O O']

def toFrac : O' ⊗[O] F →ₗ[O'] FractionRing O' ⊗[O] F :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap O' (FractionRing O')) LinearMap.id

theorem toFrac_tmul (a : O') (x : F) :
    toFrac O F O' (a ⊗ₜ x) = algebraMap O' (FractionRing O') a ⊗ₜ x := rfl

theorem toFrac_injective : Function.Injective (toFrac O F O') := by
  haveI : Module.Flat O (FractionRing O) := IsLocalization.flat _ (nonZeroDivisors O)
  haveI : Module.Flat O F := Module.Flat.trans O (FractionRing O) F
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := F)
    ((Algebra.linearMap O' (FractionRing O')).restrictScalars O) (IsFractionRing.injective O' _)
  have e : ∀ x, toFrac O F O' x =
      ((Algebra.linearMap O' (FractionRing O')).restrictScalars O).rTensor F x := by
    intro x
    induction x with
    | tmul a x => rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  intro x y hxy
  exact h (by rw [← e, ← e, hxy])

end Transport
section Objects

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

end Objects

section PartB

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

section Ext

variable (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O']

theorem eExt_toFrac (y : O' ⊗[X.O i] Y.Fm i j b) :
    ToricLatticeDenominators.eExt Y i j b O' (toFrac _ _ O' y) =
      toFrac _ _ O' ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange O' y) := by
  induction y with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_eExt (L : Submodule O' (O' ⊗[X.O i] Y.Fm i j b)) :
    (L.map (toFrac _ _ O')).map (ToricLatticeDenominators.eExt Y i j b O') =
      (L.map ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange O')).map (toFrac _ _ O') := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  exact LinearMap.ext (eExt_toFrac Y i j b O')

variable (k : ℕ) [Algebra (X.Ok i k) O'] [IsScalarTower (X.O i) (X.Ok i k) O']

def up : X.Ok i k ⊗[X.O i] Y.Fm i j b →ₗ[X.Ok i k] O' ⊗[X.O i] Y.Fm i j b :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap (X.Ok i k) O') LinearMap.id

theorem up_eq (y : X.Ok i k ⊗[X.O i] Y.Fm i j b) : up Y i j b O' k y =
    LinearMap.rTensor (Y.Fm i j b) (IsScalarTower.toAlgHom (X.O i) (X.Ok i k) O').toLinearMap y := by
  induction y with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem incl_eq (y : X.Ok i k ⊗[X.O i] Y.Fm i j b) :
    ToricLatticeDenominators.incl Y i j b O' k y = toFrac _ _ O' (up Y i j b O' k y) := by
  induction y with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem up_e (y : X.Ok i k ⊗[X.O i] Y.Fm i j b) :
    up Y i j b O' k ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange (X.Ok i k) y) =
      (Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange O' (up Y i j b O' k y) := by
  induction y with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def ext (L : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) : Submodule O' (O' ⊗[X.O i] Y.Fm i j b) :=
  Submodule.span O' (up Y i j b O' k '' L)

theorem ext_span (S : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b)) :
    ext Y i j b O' k (Submodule.span _ S) = Submodule.span O' (up Y i j b O' k '' S) := by
  rw [ext, ← Submodule.map_coe, Submodule.map_span, Submodule.span_span_of_tower]

theorem span_incl_map (S : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b)) :
    (Submodule.span O' (ToricLatticeDenominators.incl Y i j b O' k '' S)).map (ToricLatticeDenominators.eExt Y i j b O') =
      (ext Y i j b O' k ((Submodule.span _ S).map ((Formalism.MainNotions.IntegralHeckeForms.eO Y i j b).baseChange (X.Ok i k)))).map
        (toFrac _ _ O') := by
  have : Submodule.span O' (ToricLatticeDenominators.incl Y i j b O' k '' S) =
      (Submodule.span O' (up Y i j b O' k '' S)).map (toFrac _ _ O') := by
    rw [Submodule.map_span, Set.image_image]
    congr 1
    exact Set.image_congr fun x _ => incl_eq Y i j b O' k x
  rw [this, map_eExt, Submodule.map_span, Submodule.map_span (R₂ := X.Ok i k), ext_span, Set.image_image,
    Set.image_image]
  congr 2
  exact Set.image_congr fun x _ => (up_e Y i j b O' k x).symm

theorem ext_baseChange (V : Submodule (X.O i) (Y.Fm i j b)) :
    ext Y i j b O' k (V.baseChange (X.Ok i k)) = V.baseChange O' := by
  rw [Submodule.baseChange_eq_span, ext_span, Submodule.baseChange_eq_span, Submodule.map_coe,
    Submodule.map_coe, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => by simp [up]

end Ext

end PartB

section Basis

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : ℕ) (b : Bool)

theorem card_ne_zero : ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) ≠ 0 := by
  haveI : CharZero (FractionRing (X.O0 i)) := charZero_of_injective_ringHom (X.emb0 i).injective
  haveI : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  haveI : CharZero (X.O i) := charZero_of_injective_ringHom (X.O_inj i)
  exact Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'

theorem eTh_isLatIn (Sg : Set (Y.Dat i j b))
    (h : ToricLatticeDenominators.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b) ((Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Sg).map (Formalism.MainNotions.IntegralHeckeForms.AO Y i j b))) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (Formalism.MainNotions.IntegralHeckeForms.eTh Y i j b Sg) ((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)) := by
  set n : X.O i := ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) with hn
  have hn0 : algebraMap (X.O i) (FractionRing (X.O i)) n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (card_ne_zero i)
  have hinj : Function.Injective (n • LinearMap.id : Y.Fm i j b →ₗ[X.O i] Y.Fm i j b) := by
    intro x y hxy
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
    rw [← algebraMap_smul (FractionRing (X.O i)) n x, ← algebraMap_smul (FractionRing (X.O i)) n y] at hxy
    exact smul_right_injective _ hn0 hxy
  have e1 : (Formalism.MainNotions.IntegralHeckeForms.eTh Y i j b Sg).map (n • LinearMap.id) =
      (Formalism.MainNotions.IntegralHeckeForms.Th Y i j b Sg).map (Formalism.MainNotions.IntegralHeckeForms.AO Y i j b) := by
    rw [Formalism.MainNotions.IntegralHeckeForms.eTh, ← Submodule.map_comp]; rfl
  have e2 : ((Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i)).map (n • LinearMap.id) =
      (Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b).restrictScalars (X.O i) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact Submodule.smul_mem _ n hx
    · intro x hx
      refine ⟨(algebraMap (X.O i) (FractionRing (X.O i)) n)⁻¹ • x, Submodule.smul_mem (Formalism.MainNotions.IntegralHeckeForms.V0 Y i j b) _ hx, ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [← algebraMap_smul (FractionRing (X.O i)) n, smul_inv_smul₀ hn0]
  rw [← isLatIn_map_iff _ hinj, e1, e2, ← isLatIn_iff]
  exact h

variable (E : Formalism.MainNotions.IntegralHeckeForms.ExpDat Y)


end Basis

section Main

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (bkP : BKPh X)

variable (Y : NExp D.R D.host D.what₂ D.LL0 N X) (E : Formalism.MainNotions.IntegralHeckeForms.ExpDat Y)




end Main

end GlobalTheory.ExportCompare

end
