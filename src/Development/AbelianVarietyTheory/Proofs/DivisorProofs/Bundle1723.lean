module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0799
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtWAtPlSelf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

noncomputable def atW (w : Pl D.host.E) : AE D →+* Kw w := (cpt w).comp (toEAf D)

theorem atW_apply (w : Pl D.host.E) (a : AE D) : atW w a = cpt w (toEAf D a) := rfl

theorem atW_atPl_self (w : Pl D.host.E) (x : Kw w) : atW w (atPl w x) = x := by
  classical
  rw [atW_apply, (atPl_spec w x).2 w, Pi.single_eq_same]

theorem atW_atPl_ne {w w' : Pl D.host.E} (h : w ≠ w') (x : Kw w') : atW w (atPl w' x) = 0 := by
  classical
  rw [atW_apply, (atPl_spec w' x).2 w, Pi.single_eq_of_ne h]

theorem atPl_one_mul (w : Pl D.host.E) (z : Kw w) : atPl w 1 * atPl w z = atPl w z := by
  classical
  refine ae_ext (by rw [map_mul, (atPl_spec w 1).1, zero_mul, (atPl_spec w z).1]) fun Q => ?_
  rw [map_mul, map_mul, (atPl_spec w 1).2 Q, (atPl_spec w z).2 Q]
  by_cases h : Q = w
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_mul]

namespace CoordinateMaps

variable (B : Frames G) (t : T) (w : Pl D.host.E) {X Y : ℕ × ℕ} (hX : X.1 ≤ D.R.m ∧ X.2 ≤ D.R.m)
  (hY : Y.1 ≤ D.R.m ∧ Y.2 ≤ D.R.m)

theorem coord_add (y y' : Matrix (Fin (G.V (.grid X.1 X.2)).rank) (Fin (G.V (.grid Y.1 Y.2)).rank) (Kw w)) :
    B.coord t w hX hY (y + y') = B.coord t w hX hY y + B.coord t w hX hY y' := by
  unfold Frames.coord
  rw [Matrix.mul_add, Matrix.add_mul]
  rfl

theorem coord_zero : B.coord t w hX hY 0 = 0 := by
  unfold Frames.coord
  rw [Matrix.mul_zero, Matrix.zero_mul]
  rfl

theorem coord_surj (z : Matrix (Fin ((locGrid G t w).rank Y)) (Fin ((locGrid G t w).rank X)) (Kw w)) :
    ∃ y, B.coord t w hX hY y = z := by
  refine ⟨(loc w (B.β X.1 X.2)).val * (zᵀ.submatrix (Fin.cast (rank_vertex G t w hX).symm)
    (Fin.cast (rank_vertex G t w hY).symm)) * ((loc w (B.β Y.1 Y.2))⁻¹).val, ?_⟩
  unfold Frames.coord
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  ext a b
  simp only [transpose_apply, submatrix_apply, Fin.cast_cast, Fin.cast_eq_self]

end CoordinateMaps

end GlobalTheory.BigDat

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem map_atW_smul (w : Pl D.host.E) {m n : Type} (M : Matrix m n (AE D)) :
    (atPl w 1 • M).map (atW w) = M.map (atW w) := by
  refine Matrix.ext fun a b => ?_
  rw [map_apply, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, atW_atPl_self, one_mul]

theorem mixCo_eq (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E) (u : Pt G i j) :
    mixCo B t e w u = fromCols (B.coord t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      ((mapV e u).map (atW w)))
      (B.coord t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ ((mapW e u).map (atW w)))ᵀ := rfl

theorem mixCo_spec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (B : Frames G) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E),
    (∀ u x : Pt G i j, mixCo B t e w (u + x) = mixCo B t e w u + mixCo B t e w x) ∧
    (∀ z, ∃ x ∈ mixHalf e (atPl w 1), mixCo B t e w x = z) ∧
    (∀ u : Pt G i j, mixCo B t e w (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = mixCo B t e w u) ∧
    ∀ w' : Pl D.host.E, w' ≠ w → ∀ x ∈ mixHalf e (atPl w' 1), mixCo B t e w x = 0 := by
  intro D T L sc G B t i j e w
  refine ⟨fun u x => ?_, fun z => ?_, fun u => ?_, fun w' hw x hx => ?_⟩
  · rw [mixCo_eq, mixCo_eq, mixCo_eq, mapV_add, mapW_add, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _),
      CoordinateMaps.coord_add, CoordinateMaps.coord_add, transpose_add]
    exact Matrix.ext fun a b => by rcases b with b | b <;> rfl
  · obtain ⟨y₁, hy₁⟩ := CoordinateMaps.coord_surj B t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      z.toCols₁
    obtain ⟨y₂, hy₂⟩ := CoordinateMaps.coord_surj B t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
      z.toCols₂ᵀ
    let x₁ : HomV G i j := y₁.map (atPl w)
    let x₂ : HomW G i j := y₂.map (atPl w)
    have k₁ : mapV e (ofMaps e (x₁, x₂)) = x₁ := mapV_ofMaps e _
    have k₂ : mapW e (ofMaps e (x₁, x₂)) = x₂ := mapW_ofMaps e _
    have m₁ : x₁.map (atW w) = y₁ := Matrix.ext fun a b => atW_atPl_self w _
    have m₂ : x₂.map (atW w) = y₂ := Matrix.ext fun a b => atW_atPl_self w _
    refine ⟨ofMaps e (x₁, x₂), ⟨?_, ?_⟩, ?_⟩
    · show IsHalf _ (mapV e _)
      rw [k₁]
      intro a b
      exact atPl_one_mul w _
    · show IsHalf _ (mapW e _)
      rw [k₂]
      intro a b
      exact atPl_one_mul w _
    · rw [mixCo_eq, k₁, k₂, m₁, m₂, hy₁, hy₂, transpose_transpose, fromCols_toCols]
  · have k₁ : mapV e (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = atPl w 1 • mapV e u := mapV_ofMaps e _
    have k₂ : mapW e (ofMaps e (atPl w 1 • mapV e u, atPl w 1 • mapW e u)) = atPl w 1 • mapW e u := mapW_ofMaps e _
    rw [mixCo_eq, mixCo_eq, k₁, k₂, map_atW_smul, map_atW_smul]
  · have h₁ : (mapV e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapV e x a b) = atW w (atPl w' 1 * mapV e x a b) := congrArg _ (hx.1 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    have h₂ : (mapW e x).map (atW w) = 0 := by
      refine Matrix.ext fun a b => ?_
      calc atW w (mapW e x a b) = atW w (atPl w' 1 * mapW e x a b) := congrArg _ (hx.2 a b).symm
        _ = 0 := by rw [map_mul, atW_atPl_ne hw.symm, zero_mul]
    rw [mixCo_eq, h₁, h₂, CoordinateMaps.coord_zero, CoordinateMaps.coord_zero, transpose_zero, fromCols_zero]

end GlobalTheory.BigDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxGraphGraphHeis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat.GraphHeis

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {D : D7}

theorem isHalf_nsmul' {m n : ℕ} {ε : AE D} {a : Mx D m n} (ha : IsHalf ε a) (k : ℕ) : IsHalf ε (k • a) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, ha i j]

theorem isHalf_of_add' {m n : ℕ} {ε : AE D} {a b : Mx D m n} (h : IsHalf ε (a + b)) (hb : IsHalf ε b) : IsHalf ε a :=
  fun i j => by
    have h1 := h i j
    rw [Matrix.add_apply, mul_add, hb i j] at h1
    exact add_right_cancel h1

theorem sb_trans {m n : ℕ} {ε : AE D} {Λ : AddSubgroup (Mx D m n)} {φ : Mx D m n → ℂ} (h : IsSBHalf ε Λ φ)
    {x : Mx D m n} (hx : IsHalf ε x) {k₀ : ℕ} (hk₀ : 0 < k₀) (hkx : k₀ • x ∈ Λ) :
    IsSBHalf ε Λ (fun t => φ (t + x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => isHalf_of_add' (h1 _ ht) hx, k * k₀, Nat.mul_pos hk hk₀, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · show φ (t + (k * k₀) • u + x) = φ (t + x)
    rw [show t + (k * k₀) • u + x = (t + x) + k • (k₀ • u) by rw [mul_smul]; abel]
    exact h2 _ (nsmul_mem hu k₀) (isHalf_nsmul' hu' k₀) _
  · have e : (k * k₀) • t = k₀ • (k • (t + x)) - k • (k₀ • x) := by
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, mul_comm k₀ k]; abel
    rw [e]
    exact sub_mem (nsmul_mem (h3 _ ht) k₀) (nsmul_mem hkx k)

theorem sb_modul {m n : ℕ} {ε : AE D} {Λ : AddSubgroup (Mx D m n)} {φ : Mx D m n → ℂ} (h : IsSBHalf ε Λ φ)
    (χ : Mx D m n → ℂ) (hχ : ∀ a b, χ (a + b) = χ a * χ b) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (h1χ : ∀ u ∈ Λ, IsHalf ε u → χ (k₀ • u) = 1) : IsSBHalf ε Λ (fun t => χ t * φ t) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => h1 t (right_ne_zero_of_mul ht), k₀ * k, Nat.mul_pos hk₀ hk, fun u hu hu' t => ?_,
    fun t ht => ?_⟩
  · show χ (t + (k₀ * k) • u) * φ (t + (k₀ * k) • u) = χ t * φ t
    rw [hχ, mul_smul, h1χ _ (nsmul_mem hu k) (isHalf_nsmul' hu' k), mul_one, smul_comm k₀ k u,
      h2 _ (nsmul_mem hu k₀) (isHalf_nsmul' hu' k₀)]
  · rw [mul_smul]
    exact nsmul_mem (h3 t (right_ne_zero_of_mul ht)) k₀

theorem symplO_add_left' (S T : HSp D) (x x' y : WO S T) : symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  simp only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, LinearMap.map_add (f := _)]

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, RingHom.map_add (f := _), map_add (cA D), mul_add, add_mul, Finset.sum_add_distrib,
    LinearMap.map_add]

theorem symplO_nsmul' (S T : HSp D) (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  have h1 := map_nsmul (AddMonoidHom.mk' (fun x => symplO S T x y) fun a b => symplO_add_left' S T a b y) k x
  have h2 := map_nsmul (AddMonoidHom.mk' (fun y => symplO S T x y) fun a b => symplO_add_right' S T x a b) k y
  exact h1.trans h2.symm

theorem map_infPart_of_half {S T : HSp D} {a : AE D} (ha : infPart D a = 0) {u : WO S T} (hu : IsHalf a u) :
    u.map (infPart D) = 0 := by
  ext i j
  show infPart D (u i j) = 0
  rw [← hu i j, map_mul, ha, zero_mul]

theorem sb_trans_latO {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : Submodule.IsFullLattice D.host.E ΛS)
    (hT : Submodule.IsFullLattice D.host.E ΛT) {ε : AE D} (hinf : infPart D ε = 0) {φ : WO S T → ℂ}
    (h : IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) φ)
    {x : WO S T} (hx : IsHalf ε x) :
    IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun t => φ (t + x)) := by
  obtain ⟨k, hk, hkx⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO hS hT x (map_infPart_of_half hinf hx)
  exact sb_trans h hx hk hkx

theorem sb_modul_latO {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {ε : AE D} (hinf : infPart D (cA D ε) = 0) {φ : WO S T → ℂ}
    (h : IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) φ)
    {y : WO S T} (hy : IsHalf (cA D ε) y) :
    IsSBHalf ε (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (fun t => ψ (symplO S T t y) * φ t) := by
  obtain ⟨k, hk, hky⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO
    (GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS)
    (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT) y (map_infPart_of_half hinf hy)
  refine sb_modul h (fun t => ψ (symplO S T t y)) (fun a b => ?_) hk (fun u hu _ => ?_)
  · show ψ (symplO S T (a + b) y) = ψ (symplO S T a y) * ψ (symplO S T b y)
    rw [symplO_add_left', AddChar.map_add_eq_mul]
  · show ψ (symplO S T (k • u) y) = 1
    rw [symplO_nsmul']
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hu hky

end GlobalTheory.BigDat.GraphHeis

namespace GlobalTheory.BigDat

open GlobalTheory.BigDat.GraphHeis

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

def graphMap (e : Num G i j) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
    (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)) : (Pt G i j → ℂ) →ₗ[ℂ] (Pt G i j → ℂ) where
  toFun g u := T₁ (fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u)) (mapV e u)
  map_add' g g' := funext fun u => by
    have h : (fun x => T₂ (fun y => (g + g') (ofMaps e (x, y))) (mapW e u)) =
        (fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u)) + fun x => T₂ (fun y => g' (ofMaps e (x, y))) (mapW e u) :=
      funext fun x => by
        show T₂ ((fun y => g (ofMaps e (x, y))) + fun y => g' (ofMaps e (x, y))) (mapW e u) = _
        rw [map_add (f := _)]; rfl
    show T₁ (fun x => T₂ (fun y => (g + g') (ofMaps e (x, y))) (mapW e u)) (mapV e u) = _
    rw [h, map_add (f := _)]; rfl
  map_smul' c g := funext fun u => by
    have h : (fun x => T₂ (fun y => (c • g) (ofMaps e (x, y))) (mapW e u)) =
        c • fun x => T₂ (fun y => g (ofMaps e (x, y))) (mapW e u) :=
      funext fun x => by
        show T₂ (c • fun y => g (ofMaps e (x, y))) (mapW e u) = _
        rw [map_smul]; rfl
    show T₁ (fun x => T₂ (fun y => (c • g) (ofMaps e (x, y))) (mapW e u)) (mapV e u) = _
    rw [h, map_smul]; rfl

theorem graphMap_box (e : Num G i j) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
    (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)) (φ₁ : HomV G i j → ℂ) (φ₂ : HomW G i j → ℂ) :
    graphMap e T₁ T₂ (box e φ₁ φ₂) = box e (T₁ φ₁) (T₂ φ₂) := funext fun u => by
  have e2 : ∀ x, (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) = φ₁ x • φ₂ := fun x => funext fun y => by
    show φ₁ (mapV e (ofMaps e (x, y))) * φ₂ (mapW e (ofMaps e (x, y))) = φ₁ x * φ₂ y
    rw [mapV_ofMaps, mapW_ofMaps]
  have e1 : (fun x => T₂ (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) (mapW e u)) = T₂ φ₂ (mapW e u) • φ₁ :=
    funext fun x => by
      rw [e2, map_smul]
      show φ₁ x * T₂ φ₂ (mapW e u) = T₂ φ₂ (mapW e u) * φ₁ x
      exact mul_comm _ _
  show T₁ (fun x => T₂ (fun y => box e φ₁ φ₂ (ofMaps e (x, y))) (mapW e u)) (mapV e u) = T₁ φ₁ (mapV e u) * T₂ φ₂ (mapW e u)
  rw [e1, map_smul]
  show T₂ φ₂ (mapW e u) * T₁ φ₁ (mapV e u) = _
  exact mul_comm _ _

def transPair (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (x : Pt G i j) :
    ((Pt G i j → ℂ) × (Pt G i j → ℂ)) →ₗ[ℂ] ((Pt G i j → ℂ) × (Pt G i j → ℂ)) where
  toFun p := (fun u => p.1 (u + x), heisPt Γ ψ x p.2)
  map_add' p q := Prod.ext rfl (funext fun u => mul_add _ _ _)
  map_smul' c p := Prod.ext rfl (funext fun u => mul_left_comm _ _ _)

def modulPair (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (y : Pt G i j) :
    ((Pt G i j → ℂ) × (Pt G i j → ℂ)) →ₗ[ℂ] ((Pt G i j → ℂ) × (Pt G i j → ℂ)) where
  toFun p := (fun u => ψ (sympPt Γ u y) * p.1 u, heisPt Γ ψ y p.2)
  map_add' p q := Prod.ext (funext fun u => mul_add _ _ _) (funext fun u => mul_add _ _ _)
  map_smul' c p := Prod.ext (funext fun u => mul_left_comm _ _ _) (funext fun u => mul_left_comm _ _ _)

end GlobalTheory.BigDat


set_option maxHeartbeats 1600000 in
open GlobalTheory.BigDat.GraphHeis in
theorem GlobalTheory.BigDat.boxGraph_graph_heis : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ (ε : AE D) (P : Finset (Pl D.host.E)), IsIdemSum ε P →
    ∀ (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
      (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)),
    IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) ε (latV G i j) 1 f₁ T₁ →
    IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) ε (latW G i j) 1 f₂ T₂ →
    (∀ f, (0, f) ∈ boxGraph e ε T₁ T₂ → f = 0) ∧
    (∀ x ∈ mixHalf e ε, ∀ p ∈ boxGraph e ε T₁ T₂, (fun u => p.1 (u + x), heisPt Γ W.ψ x p.2) ∈ boxGraph e ε T₁ T₂) ∧
    ∀ y ∈ mixHalf e (cA D ε), ∀ p ∈ boxGraph e ε T₁ T₂,
      (fun u => W.ψ (sympPt Γ u y) * p.1 u, heisPt Γ W.ψ y p.2) ∈ boxGraph e ε T₁ T₂ := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW ε P hε f₁ f₂ T₁ T₂ h₁ h₂
  have hinf : infPart D ε = 0 := GlobalTheory.PlaceVec.idemSum_infPart hε
  have hinf' : infPart D (cA D ε) = 0 := GlobalTheory.PlaceVec.infPart_cA hinf
  have sdW : IsSelfDualC (spW G i j) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  have sdV : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have sdV₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have sdW' : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) := isSelfDualC_neg sdW
  refine ⟨fun f hf => ?_, fun x hx p hp => ?_, fun y hy p hp => ?_⟩
  · have key : boxGraph e ε T₁ T₂ ≤ LinearMap.ker (LinearMap.snd ℂ _ _ - graphMap e T₁ T₂ ∘ₗ LinearMap.fst ℂ _ _) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, -, -, rfl⟩ := hp
      show box e (T₁ φ₁) (T₂ φ₂) - graphMap e T₁ T₂ (box e φ₁ φ₂) = 0
      rw [graphMap_box, sub_self]
    have h0 := key hf
    rw [LinearMap.mem_ker] at h0
    have h1 : f - graphMap e T₁ T₂ 0 = 0 := h0
    rwa [map_zero, sub_zero] at h1
  · have key : boxGraph e ε T₁ T₂ ≤ (boxGraph e ε T₁ T₂).comap (transPair Γ W.ψ x) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, hφ₁, hφ₂, rfl⟩ := hp
      have hx₁ : IsHalf ε (mapV e x) := hx.1
      have hx₂ : IsHalf ε (mapW e x) := hx.2
      have s₁ : IsSBHalf ε (latV G i j) (fun t => φ₁ (t + mapV e x)) :=
        sb_trans_latO (S := negSp (spW G i j)) (T := spV G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))
          (ΛT := G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) (GlobalTheory.PlaceVec.selfDual_isFullLattice (negSp (spW G i j)) _ sdW')
          (GlobalTheory.PlaceVec.selfDual_isFullLattice (spV G i j) _ sdV) hinf hφ₁ hx₁
      have s₂ : IsSBHalf ε (latW G i j) (fun t => φ₂ (t + mapW e x)) :=
        sb_trans_latO (S := spV₁ G i j) (T := spW G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))
          (ΛT := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) (GlobalTheory.PlaceVec.selfDual_isFullLattice (spV₁ G i j) _ sdV₁)
          (GlobalTheory.PlaceVec.selfDual_isFullLattice (spW G i j) _ sdW) hinf hφ₂ hx₂
      show (fun u => box e φ₁ φ₂ (u + x), heisPt Γ W.ψ x (box e (T₁ φ₁) (T₂ φ₂))) ∈ boxGraph e ε T₁ T₂
      rw [heisPt_box e Γ hW hWW]
      refine Submodule.subset_span ⟨_, _, s₁, s₂, ?_⟩
      rw [h₁.trans φ₁ hφ₁ _ hx₁, h₂.trans φ₂ hφ₂ _ hx₂]
      refine Prod.ext (funext fun u => ?_) rfl
      show φ₁ (mapV e (u + x)) * φ₂ (mapW e (u + x)) = φ₁ (mapV e u + mapV e x) * φ₂ (mapW e u + mapW e x)
      rw [mapV_add, mapW_add]
    exact key hp
  · have key : boxGraph e ε T₁ T₂ ≤ (boxGraph e ε T₁ T₂).comap (modulPair Γ W.ψ y) := by
      refine Submodule.span_le.2 fun p hp => ?_
      obtain ⟨φ₁, φ₂, hφ₁, hφ₂, rfl⟩ := hp
      have hy₁ : IsHalf (cA D ε) (mapV e y) := hy.1
      have hy₂ : IsHalf (cA D ε) (mapW e y) := hy.2
      have s₁ : IsSBHalf ε (latV G i j) (fun t => W.ψ (symplO _ _ t (mapV e y)) * φ₁ t) :=
        sb_modul_latO (S := negSp (spW G i j)) (T := spV G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))
          (ΛT := G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) W.ψ_std sdW' sdV hinf' hφ₁ hy₁
      have s₂ : IsSBHalf ε (latW G i j) (fun t => W.ψ (symplO _ _ t (mapW e y)) * φ₂ t) :=
        sb_modul_latO (S := spV₁ G i j) (T := spW G i j) (ΛS := G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))
          (ΛT := G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) W.ψ_std sdV₁ sdW hinf' hφ₂ hy₂
      show (fun u => W.ψ (sympPt Γ u y) * box e φ₁ φ₂ u, heisPt Γ W.ψ y (box e (T₁ φ₁) (T₂ φ₂))) ∈ boxGraph e ε T₁ T₂
      rw [heisPt_box e Γ hW hWW]
      refine Submodule.subset_span ⟨_, _, s₁, s₂, ?_⟩
      rw [h₁.modul φ₁ hφ₁ _ hy₁, h₂.modul φ₂ hφ₂ _ hy₂]
      refine Prod.ext (funext fun u => ?_) rfl
      show W.ψ (sympPt Γ u y) * (φ₁ (mapV e u) * φ₂ (mapW e u)) =
        (W.ψ (symplO _ _ (mapV e u) (mapV e y)) * φ₁ (mapV e u)) * (W.ψ (symplO _ _ (mapW e u) (mapW e y)) * φ₂ (mapW e u))
      rw [symp_eq e Γ hW hWW, AddChar.map_add_eq_mul]
      ring
    exact key hp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeOfIsIdemAt
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum

theorem conj_smul_ne_of_isIdemAt {D : D7} {e : Formalism.L2.Theta.AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) : D.host.conj • P.asIdeal ≠ P.asIdeal := by
  intro h
  have hc := GlobalTheory.EtaProduct.cA_of_fixed (GlobalTheory.HeckeDetChar.isPlIdem he) h
  have h0 : e = 0 := by
    have := he.1.2.1
    rw [hc, he.1.1] at this
    exact this
  apply P.ne_bot
  refine eq_bot_iff.2 fun x hx => ?_
  by_contra hx0
  have := (he.2 x hx0).1 hx
  rw [h0, zero_mul, map_zero] at this
  exact this (zero_mem _)

theorem condE_isCoprime_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L),
    IsCoprime (condE P) (D.host.conj • condE P) := by
  intro D T L P
  have hF : ∀ I : Ideal (𝓞 D.host.E), (D.host.conj • I).under (𝓞 D.host.F) = I.under (𝓞 D.host.F) :=
    GlobalTheory.PlaceOverPair.under_smul_of_fix D.host.conj
      (fun x => (D.host.conjE_mem_hostF_iff _).1 x.2)
  unfold GlobalTheory.FunObj.SqNum.condE
  rw [Finset.smul_prod']
  refine IsCoprime.prod_left fun v hv => IsCoprime.prod_right fun v' hv' => ?_
  rw [smul_pow']
  refine IsCoprime.pow ?_
  rw [Ideal.isCoprime_iff_sup_eq]
  have hm : (D.host.conj • (P.w v').asIdeal).IsMaximal := by
    have := (P.w v').isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => (P.w v').ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  refine Ideal.IsMaximal.coprime_of_ne (P.w v).isMaximal hm fun heq => ?_
  have hvv : v = v' := by
    have a := congrArg HeightOneSpectrum.asIdeal (P.under_w hv)
    have b := congrArg HeightOneSpectrum.asIdeal (P.under_w hv')
    refine HeightOneSpectrum.ext ?_
    rw [← a, ← b]
    show Ideal.under _ _ = Ideal.under _ _
    rw [heq, hF]
  subst hvv
  obtain ⟨e, he⟩ := P.w_split v hv
  exact conj_smul_ne_of_isIdemAt he heq.symm

end GlobalTheory.FunObj.StdDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinateChangeRealisedWithDoubleStatement
section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxCoordinateChange_realised_with_double : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsStd ψ → ∀ (α β κ κ' : Type) [Fintype α] [Fintype β] [Fintype κ] [Fintype κ'] (B : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F) (d : Darboux B κ) (d' : Darboux B κ'), IsRat d → IsRat d' → ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (fun w => d'.e (d.e.symm w)) S S' := by
  first | exact @GlobalTheory.TowU.darboux_change | exact GlobalTheory.TowU.darboux_change | (intros; apply GlobalTheory.TowU.darboux_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenvalueEqOneInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  first | exact @GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag | exact GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag | (intros; apply GlobalTheory.DblVacSiegelV.eigen_eq_one_of_diag <;> assumption)
end

