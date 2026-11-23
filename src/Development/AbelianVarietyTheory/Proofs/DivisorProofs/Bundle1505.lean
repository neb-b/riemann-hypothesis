module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

open Filter Topology

variable {D : D7}

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem inBasis_apply {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).1 i j = cpt w ((β⁻¹ * x * β).1 (finCongr h i) (finCongr h j)) := rfl

theorem inBasis_mem_KO {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (hx : x ∈ St β) (w : Pl D.host.E) :
    inBasis rfl β w x ∈ KO (Kw w) (Fin n) := by
  obtain ⟨y, rfl⟩ := hx
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  have hm : ∀ z : GL (Fin n) (Lev.EAf D), z ∈ ({Formalism.L2.DIV.intGL _ _ n y, (Formalism.L2.DIV.intGL _ _ n y)⁻¹} : Set _) →
      ∀ a b, cpt w (z.1 a b) ∈ Formalism.UG.Ov D.host.E w := by
    intro z hz a b
    refine (mem_OA_iff _).1 ?_ w
    rcases hz with rfl | rfl
    · exact (y.1 a b).2
    · rw [← map_inv]; exact ((y⁻¹).1 a b).2
  have e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y := by
    simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  have e2 : β⁻¹ * (Formalism.L2.DIV.frGL β y)⁻¹ * β = (Formalism.L2.DIV.intGL _ _ n y)⁻¹ := by
    rw [← e1]; group
  refine mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [inBasis_apply, e1]; exact hm _ (Or.inl rfl) _ _
  · rw [← map_inv, inBasis_apply, e2]; exact hm _ (Or.inr rfl) _ _

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGlLatCongOfSmul
section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model ValuativeRel
open scoped Pointwise

noncomputable section
namespace GlobalTheory.FrameDepth

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D : Type*} [Fintype D] [DecidableEq D]

theorem conj_mem_glLatCong {Λ Λ' : Submodule 𝒪[k] (D → k)} {u : kˣ} (G : GL D k)
    (hG : ∀ x, x ᵥ* G.val ∈ Λ' ↔ x ∈ Λ) {g : GL D k} (hg : g ∈ glLatCong u Λ') :
    G * g * G⁻¹ ∈ glLatCong u Λ := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [← hG, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, ← vecMul_vecMul, hg.1, hG]
  · have h1 := hg.2 _ ((hG x).2 hx)
    rw [mem_smul_lat] at h1 ⊢
    rw [← hG]
    convert h1 using 1
    rw [Units.smul_def, Units.smul_def, smul_vecMul, vecMul_vecMul, vecMul_vecMul, sub_mul, mul_sub,
      ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, mul_one, one_mul]

theorem vecMul_diagGL_mem (b c d : D → kˣ) (h : ∀ j, d j = b j * c j) (x : D → k) :
    x ᵥ* (diagGL c).val ∈ diagLat d ↔ x ∈ diagLat b := by
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
  rw [diagGL_val, vecMul_diagonal, map_mul, h, Units.val_mul, map_mul]
  exact mul_le_mul_iff_left₀ h0

theorem mem_glLatCong_of_smul {Λ : Submodule 𝒪[k] (D → k)} {u v : kˣ} {g : GL D k}
    (hg : g ∈ glLatCong u (v • Λ)) : g ∈ glLatCong u Λ := by
  have hm : ∀ x, v • x ∈ v • Λ ↔ x ∈ Λ := fun x => by rw [mem_smul_lat, inv_smul_smul]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [← hm, ← hm x, ← hg.1 (v • x), Units.smul_def v x, smul_vecMul, ← Units.smul_def v (x ᵥ* g.val)]
  · have h1 := hg.2 _ ((hm x).2 hx)
    rw [mem_smul_lat, mem_smul_lat] at h1
    rw [mem_smul_lat]
    convert h1 using 1
    rw [smul_comm v⁻¹, Units.smul_def v, smul_vecMul, ← Units.smul_def v, inv_smul_smul]

theorem invT_mem_of_dual {u : kˣ} {c : D → kˣ} {g : GL D k} (hg : g ∈ glLatCong u (dualLat (diagLat c))) :
    invT g ∈ glLatCong u (diagLat c) ∧ gdet (invT g) ∈ unitCong u := by
  rw [dualLat_diagLat] at hg
  have h1 := GlobalTheory.FunObj.GivenAdm.invT_mem_glLatCong (conj_mem_glLatCong (Λ := stdLat k D)
    (diagGL fun j => (c j)⁻¹) (vecMul_diagGL_mem 1 _ _ (by simp)) hg)
  have h2 : invT (diagGL fun j => (c j)⁻¹) = diagGL c := by
    rw [← _root_.inv_inj]
    refine Units.ext ?_
    rw [invT_inv_val, diagGL_val, diagonal_transpose]
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    simp [diagGL_val]
  rw [map_mul, map_mul, map_inv, h2] at h1
  constructor
  · have h3 := conj_mem_glLatCong (Λ := diagLat c) (diagGL c)⁻¹ (fun x => by
      rw [stdLat, ← vecMul_diagGL_mem 1 c c (by simp), vecMul_vecMul, Units.inv_mul, vecMul_one]) h1
    simpa [mul_assoc] using h3
  · have h3 := GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong h1
    rwa [gdet_mul, gdet_mul, show gdet (diagGL c)⁻¹ = (gdet (diagGL c))⁻¹ from map_inv _ _,
      mul_inv_cancel_comm] at h3

theorem HasDepth.mul_glLatCong {A : Type*} {ϖ : kˣ} {e : ℕ} {Λ : Submodule 𝒪[k] (D → k)}
    {Ψ : Matrix A D k → ℂ} (h : HasDepth ϖ e Λ Ψ) {g : GL D k} (hg : g ∈ glLatCong (ϖ ^ e) Λ)
    (Y : Matrix A D k) : Ψ (Y * g.val) = Ψ Y := by
  have hr : ∀ (M : Matrix D D k) i, (Y * M).row i = Y.row i ᵥ* M := fun M i => by
    funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  by_cases hY : Y ∈ matLat A Λ
  · rw [show Y * g.val = Y + Y * (g.val - 1) by rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]]
    exact h.2 _ _ fun i => by rw [hr]; exact hg.2 _ (hY i)
  · rw [h.1 _ hY, h.1 _ fun H => hY fun i => (hg.1 _).1 (by rw [← hr]; exact H i)]

theorem hasDepth_phiA (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype D] [DecidableEq D] (μ : Measure (GL A' k)) [hμ : μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ)
    (ϖ : kˣ) (e : ℕ) (c : D → kˣ) (Ψ : Matrix A' D k → ℂ) (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν)
    (hΨ : HasDepth ϖ e (diagLat c) Ψ) :
    HasDepth ϖ e (latA ϖ e (diagLat c)) (phiA μ σ ν ϖ e (diagLat c) Ψ) := by
  have hlt : valuation k ((ϖ ^ e : kˣ) : k) < 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_lt_one₀ zero_le' (hϖ ▸ uniformizer_lt_one) (by omega)
  have key : ∀ X Z : Matrix A D k, IsPrimFrame (latA ϖ e (diagLat c)) X →
      Z ∈ matLat A (ϖ ^ e • latA ϖ e (diagLat c)) → ∃ κ ∈ glLatCong (ϖ ^ e) (latA ϖ e (diagLat c)),
        X + Z = X * κ.val := by
    rw [latA, dualLat_diagLat, smul_diagLat]
    exact GlobalTheory.PrimFrameMove.exists_glLatCong_move k A D _ _ hlt
  have prim : ∀ X Z : Matrix A D k, IsPrimFrame (latA ϖ e (diagLat c)) X →
      Z ∈ matLat A (ϖ ^ e • latA ϖ e (diagLat c)) → IsPrimFrame (latA ϖ e (diagLat c)) (X + Z) := by
    intro X Z hX hZ
    obtain ⟨κ, hκ, h⟩ := key X Z hX hZ
    rw [h]
    exact GlobalTheory.SplitFlip.Model.isPrimFrame_mul hX κ hκ.1
  refine ⟨fun X hX => if_neg fun h => hX h.2.1, fun X Z hZ => ?_⟩
  by_cases hX : IsPrimFrame (latA ϖ e (diagLat c)) X
  · unfold phiA
    rw [if_pos hX, if_pos (prim X Z hX hZ)]
    obtain ⟨κ, hκ, h⟩ := key X Z hX hZ
    obtain ⟨h1, h2⟩ := invT_mem_of_dual (mem_glLatCong_of_smul hκ)
    obtain ⟨g, rfl⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).1 hX.1
    have h3 : X0 k σ * (invT g).val * κ.val = X0 k σ * (invT (g * invT κ)).val := by
      rw [map_mul, invT_invT, Units.val_mul, Matrix.mul_assoc]
    have hf := @splitTheta_fFun_frameFirstBlock_mul k _ _ _ _ A A' D _ _ _ _ _ _ _ _ μ hμ σ ν Ψ
    rw [h, h3, hf, hf, gdet_mul, map_mul, apow_mul, hν _ h2, apow_of_valuation_eq_one h2.1,
      mul_one, mul_one]
    congr 1
    simp only [smallF, Units.val_mul, ← Matrix.mul_assoc, HasDepth.mul_glLatCong hΨ h1]
  · have hX' : ¬ IsPrimFrame (latA ϖ e (diagLat c)) (X + Z) := fun h => hX (by
      simpa using prim _ (-Z) h (neg_mem hZ))
    unfold phiA
    rw [if_neg hX, if_neg hX']

end GlobalTheory.FrameDepth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismOpenAffineLineAbelianSchemeConst
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.NoRatCurve

section
variable (k : Type) [Field k] (P : Polynomial k)

def rhoMap : Localization.Away (Polynomial.X : Polynomial k) →+* Localization.Away (Polynomial.X * P) :=
  IsLocalization.Away.awayToAwayRight (S := Localization.Away (Polynomial.X : Polynomial k))
    (P := Localization.Away (Polynomial.X * P)) (Polynomial.X : Polynomial k) P

theorem rhoMap_algebraMap (x : Polynomial k) :
    rhoMap k P (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) x) =
      algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) x :=
  IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away (Polynomial.X : Polynomial k))
    (P := Localization.Away (Polynomial.X * P)) _ _ x

theorem rhoMap_invSelf : rhoMap k P (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k)) =
    algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
      IsLocalization.Away.invSelf (Polynomial.X * P) := by
  have hu1 : IsUnit (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) Polynomial.X) :=
    isUnit_of_mul_isUnit_left (x := algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) Polynomial.X)
      (y := algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P)
      (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit _)
  apply hu1.mul_left_cancel
  calc _ = rhoMap k P (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X : Polynomial k)) := by rw [map_mul, rhoMap_algebraMap]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := by rw [← _root_.mul_assoc, ← map_mul, IsLocalization.Away.mul_invSelf]

theorem rhoMap_comp_algebraMap : (rhoMap k P).comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) =
    algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) :=
  RingHom.ext (rhoMap_algebraMap k P)

theorem rhoMap_comp_aeval : (rhoMap k P).comp (Polynomial.aeval (R := k) (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
      Localization.Away (Polynomial.X : Polynomial k))).toRingHom =
    (Polynomial.aeval (R := k) (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
      IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have e1 : (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))) (Polynomial.C a) =
        algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) (Polynomial.C a) := by
      rw [Polynomial.aeval_C]; rfl
    have e2 : (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
        IsLocalization.Away.invSelf (Polynomial.X * P))) (Polynomial.C a) =
        algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) (Polynomial.C a) := by
      rw [Polynomial.aeval_C]; rfl
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e1, e2,
      rhoMap_algebraMap]
  · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_X, Polynomial.aeval_X]
    exact rhoMap_invSelf k P

end

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem awayToAwayRight_injective (k : Type) [Field k] (P : Polynomial k) (hP : P ≠ 0) :
    Function.Injective (rhoMap k P) := by
  have hXP : (Polynomial.X * P : Polynomial k) ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hP
  have hinj : Function.Injective (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P))) :=
    IsLocalization.injective (Localization.Away (Polynomial.X * P)) (powers_le_nonZeroDivisors_of_noZeroDivisors hXP)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (Polynomial.X : Polynomial k)) z
  have e := rhoMap_algebraMap k P a
  have h1 : IsLocalization.mk' (Localization.Away (Polynomial.X : Polynomial k)) a s *
      algebraMap _ _ (s : Polynomial k) = algebraMap _ _ a := IsLocalization.mk'_spec _ _ _
  have h2 := congrArg (rhoMap k P) h1
  rw [map_mul, hz, zero_mul, e] at h2
  have ha : a = 0 := hinj (by rw [← h2, map_zero])
  subst ha
  simp

theorem extend_to_line : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k), P ≠ 0 → ∀ u : Sp (Localization.Away P) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away P)) → ∃ v : Sp (Polynomial k) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Polynomial k)) ∧ spMap (algebraMap (Polynomial k) (Localization.Away P)) ≫ v = u := by
  intro k _ _ B _ _ P hP
  induction hn : P.natDegree generalizing P with
  | zero =>
    intro u hu
    obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.1 hn
    have ha : IsUnit (Polynomial.C a) := Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 (by rintro rfl; simp at hP))
    let φ : Localization.Away (Polynomial.C a) →+* Polynomial k := IsLocalization.Away.lift (g := RingHom.id (Polynomial k)) (Polynomial.C a) ha
    have hφ : (algebraMap (Polynomial k) (Localization.Away (Polynomial.C a))).comp φ = RingHom.id _ :=
      IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.C a)) (RingHom.ext fun x => by
        simp [φ, IsLocalization.Away.lift, IsLocalization.lift_eq])
    refine ⟨spMap φ ≫ u, ?_, ?_⟩
    · rw [Category.assoc, hu, ← spMap_comp']
      congr 1
      refine RingHom.ext fun x => ?_
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (Polynomial.C a))]
      simp [φ, IsLocalization.Away.lift, IsLocalization.lift_eq]
    · rw [← Category.assoc, ← spMap_comp', hφ]
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ u = u
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  | succ n ih =>
    intro u hu
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_root P (by rw [Polynomial.degree_eq_natDegree hP, hn]; exact_mod_cast Nat.succ_ne_zero n)
    obtain ⟨P', rfl⟩ : ∃ P', P = P' * (Polynomial.X - Polynomial.C c) :=
      ⟨P /ₘ (Polynomial.X - Polynomial.C c), by rw [mul_comm, Polynomial.mul_divByMonic_eq_iff_isRoot.2 hc]⟩
    have hP' : P' ≠ 0 := left_ne_zero_of_mul hP
    have hn' : P'.natDegree = n := by
      rw [Polynomial.natDegree_mul hP' (Polynomial.X_sub_C_ne_zero c), Polynomial.natDegree_X_sub_C] at hn
      omega
    obtain ⟨v', hv', ev'⟩ := GlobalTheory.T.extend_affineLine_morphism_to_proper_across_point k B P' c hP' u hu
    obtain ⟨v, hv, ev⟩ := ih P' hP' hn' v' hv'
    refine ⟨v, hv, ?_⟩
    rw [← ev', ← ev, ← Category.assoc, ← spMap_comp']
    congr 2
    exact RingHom.ext fun x => (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away P')
      (P := Localization.Away (P' * (Polynomial.X - Polynomial.C c))) P' (Polynomial.X - Polynomial.C c) x).symm

theorem maps_from_open_line_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ B.left) (a b : Localization.Away P →ₐ[k] k), u ≫ B.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u = spMap b.toRingHom ≫ u := by
  intro k _ _ B _ hB P hP u a b hu
  haveI := hB.smooth
  haveI := hB.proper
  obtain ⟨Q, hQ, σ, τ, h1, h2⟩ := GlobalTheory.T.exists_inversion_coordinate_localization_polynomial k P hP
  obtain ⟨f₀, hf₀, e₀⟩ := extend_to_line k B P hP u hu
  have hu' : (spMap σ.toRingHom ≫ u) ≫ B.hom = spMap (algebraMap k (Localization.Away Q)) := by
    rw [Category.assoc, hu, ← spMap_comp']
    congr 1
    ext x
    exact σ.commutes x
  obtain ⟨f₁, hf₁, e₁⟩ := extend_to_line k B Q hQ _ hu'
  haveI : IsDominant (spMap (rhoMap k P)) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (rhoMap k P))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (awayToAwayRight_injective k P hP)]
    exact bot_le
  have hc : spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ := by
    refine ext_of_isDominant_of_isSeparated B.hom ?_ (spMap (rhoMap k P)) ?_
    · rw [Category.assoc, Category.assoc, hf₀, hf₁, ← spMap_comp', ← spMap_comp']
      congr 1
      refine RingHom.ext fun x => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
    · calc spMap (rhoMap k P) ≫ spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀
          = spMap ((rhoMap k P).comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)))) ≫ f₀ := by
            rw [spMap_comp' (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) (rhoMap k P),
              Category.assoc]
        _ = spMap τ.toRingHom ≫ spMap σ.toRingHom ≫ u := by
            rw [rhoMap_comp_algebraMap, ← h1, spMap_comp', Category.assoc, e₀]
            show spMap (τ.toRingHom.comp σ.toRingHom) ≫ u = _
            rw [spMap_comp', Category.assoc]
        _ = spMap (τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q))) ≫ f₁ := by
            rw [spMap_comp', Category.assoc, e₁]
        _ = _ := by
            rw [h2, ← rhoMap_comp_aeval, spMap_comp', Category.assoc]
  have key := _root_.GlobalTheory.LineConst.projLine_map_const k B hB f₀ f₁ hf₀ hf₁ hc
    (a.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away P)))
    (b.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away P)))
  rw [← e₀, ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp']
  exact key

end GlobalTheory.NoRatCurve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulLintegralRpowLeOfShellBound
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

theorem exists_shell_of_le_one {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    ∃ j : ℕ, Real.exp (-(j + 1 : ℝ)) < t ∧ t ≤ Real.exp (-(j : ℝ)) := by
  have hl : 0 ≤ -Real.log t := by
    have := Real.log_nonpos h0.le h1
    linarith
  refine ⟨⌊-Real.log t⌋₊, ?_, ?_⟩
  · have := Nat.lt_floor_add_one (-Real.log t)
    rw [← Real.lt_log_iff_exp_lt h0]
    linarith
  · have := Nat.floor_le hl
    rw [← Real.log_le_iff_le_exp h0]
    linarith

theorem le_two_mul_one_sub_exp_neg {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ε ≤ 2 * (1 - Real.exp (-ε)) := by
  have h2 : ε + 1 ≤ Real.exp ε := Real.add_one_le_exp ε
  have h3 : Real.exp (-ε) * Real.exp ε = 1 := by rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-ε) := Real.exp_pos _
  have h5 : Real.exp (-ε) * (ε + 1) ≤ 1 := by nlinarith
  by_contra hc
  push Not at hc
  nlinarith

theorem mul_lintegral_rpow_le_of_shell_bound :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (h : X → ℝ) (d : ℝ) (B : ℝ≥0∞), Measurable h → (∀ x, 0 < h x) → 0 < d → (∀ j : ℕ, μ {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (d * j))) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ε * ∫⁻ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0) ∂μ ≤ 2 * B := by
  intro X _ μ h d B hm hpos hd hB ε hε0 hε1
  set S : ℕ → Set X := fun j =>
    {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} with hS
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (measurableSet_lt measurable_const hm).inter (measurableSet_le hm measurable_const)
  set c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (Real.exp (-((d + ε) * j))) with hc
  have hpt : ∀ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0)
      ≤ ∑' j, (S j).indicator (fun _ => c j) x := by
    intro x
    split_ifs with hx
    · obtain ⟨j, hj⟩ := exists_shell_of_le_one (hpos x) hx
      refine le_trans ?_ (ENNReal.le_tsum j)
      have hxS : x ∈ S j := hj
      rw [Set.indicator_of_mem hxS]
      apply ENNReal.ofReal_le_ofReal
      calc h x ^ (d + ε) ≤ (Real.exp (-(j : ℝ))) ^ (d + ε) :=
            Real.rpow_le_rpow (hpos x).le hj.2 (by linarith)
        _ = Real.exp (-((d + ε) * j)) := by
            rw [← Real.exp_mul]; congr 1; ring
    · exact zero_le
  set r : ℝ := Real.exp (-ε) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]; linarith
  have hint : ∫⁻ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0) ∂μ
      ≤ B * (1 - ENNReal.ofReal r)⁻¹ := by
    calc _ ≤ ∫⁻ x, ∑' j, (S j).indicator (fun _ => c j) x ∂μ := lintegral_mono hpt
      _ = ∑' j, ∫⁻ x, (S j).indicator (fun _ => c j) x ∂μ :=
          lintegral_tsum fun j => (measurable_const.indicator (hSm j)).aemeasurable
      _ ≤ ∑' j, B * (ENNReal.ofReal r) ^ j := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          rw [lintegral_indicator_const (hSm j)]
          calc c j * μ (S j) ≤ c j * (B * ENNReal.ofReal (Real.exp (d * j))) := by
                gcongr
                exact hB j
            _ = B * (c j * ENNReal.ofReal (Real.exp (d * j))) := by ring
            _ = B * (ENNReal.ofReal r) ^ j := by
                congr 1
                rw [hc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_pow hr0.le,
                  hr, ← Real.exp_add, ← Real.exp_nat_mul]
                congr 2; ring
      _ = B * (1 - ENNReal.ofReal r)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hkey : ENNReal.ofReal ε * (1 - ENNReal.ofReal r)⁻¹ ≤ 2 := by
    have e1 : (1 : ℝ≥0∞) - ENNReal.ofReal r = ENNReal.ofReal (1 - r) := by
      rw [ENNReal.ofReal_sub _ hr0.le, ENNReal.ofReal_one]
    have hp : 0 < 1 - r := by linarith
    rw [e1, ← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_mul hε0.le,
      ← ENNReal.ofReal_ofNat 2]
    apply ENNReal.ofReal_le_ofReal
    rw [← div_eq_mul_inv, div_le_iff₀ hp]
    exact le_two_mul_one_sub_exp_neg hε0 hε1
  calc _ ≤ ENNReal.ofReal ε * (B * (1 - ENNReal.ofReal r)⁻¹) := by gcongr
    _ = (ENNReal.ofReal ε * (1 - ENNReal.ofReal r)⁻¹) * B := by ring
    _ ≤ 2 * B := by gcongr

end GlobalTheory.ResLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyAcyclicOfCechVanishingAllCovers
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem isRelAcyclic_of_not_NV : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (P : LB A.left),
    (∀ j : ℕ, ¬ NV A P (j + 1)) → GlobalTheory.CxForm.IsRelAcyclic A.hom A.hom P := by
  intro K _ A _ P hP U _ κ _ _ W hW hWU n
  by_cases hU : U = ⊤
  · subst hU
    have hWU' : ⨆ i, W i = ⊤ := by rw [hWU]; simp
    by_contra h
    exact hP n ⟨κ, inferInstance, inferInstance, W, hW, hWU', h⟩
  · have hb : U = ⊥ := by
      refine eq_bot_iff.2 fun x hx => (hU (eq_top_iff.2 fun y _ => ?_)).elim
      have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
      rwa [Subsingleton.elim y x]
    subst hb
    refine HomologicalComplex.ExactAt.of_isZero ?_
    rw [GlobalTheory.AbLaw.cechLB_X, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun a b => funext fun s => ?_⟩
    refine GlobalTheory.AbLaw.SecOnR.ext_of_cover _ (I := PEmpty) (fun i => i.elim) (fun i => i.elim) ?_ fun i => i.elim
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos _ : 0 < s.1.card)
    refine (biInf_le W hi).trans (((le_iSup W i).trans hWU.le).trans ?_)
    simp

end GlobalTheory.AmpleGen
end
end

