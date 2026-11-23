module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TautologicalFamilyRefinementCompatibleLieAlgebra
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.TieUp

theorem exists_lift {ι : Type} {m k : ι → ℕ} {R K : Type} [CommRing R] [Field K] (a : R →+* K)
    (ha : Function.Injective a) {O : Subring K} (hO : ∀ x ∈ O, ∃ r, a r = x) {G : Mat m K} (hG : Par k O G) :
    ∃ G' : Mat m R, G'.map a = G ∧ ∀ τ, IsUnit (G' τ).det := by
  have h1 : ∀ τ i j, ∃ r, a r = G τ i j := fun τ i j => hO _ ((hG τ).1 i j)
  choose G' hG' using h1
  let G'' : Mat m R := fun τ => Matrix.of (G' τ)
  have e : G''.map a = G := by
    funext τ; ext i j; exact hG' τ i j
  refine ⟨G'', e, fun τ => ?_⟩
  obtain ⟨r, hr⟩ := hO _ (hG τ).2.2.1
  have hd : a (G'' τ).det = (G τ).det := by
    rw [← e]; exact a.map_det (G'' τ)
  refine IsUnit.of_mul_eq_one r (ha ?_)
  rw [map_mul, hd, hr, map_one, mul_inv_cancel₀ (hG.det_ne τ)]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B Y : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (k : (E →+* ℂ) → ℕ) (S' : Fr (ratOf Y) Dw.mult k) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X), Tied e B j f₀ S A₀ → Refines S S' φ f → ∃ (g₀ : EigFrame Z (constF e Y) (genericPt Y ≫ (f ≫ j) ≫ genι Z)) (A₁ : Mat Dw.mult Y.Fn), Tied e Y (f ≫ j) g₀ S' A₁ ∧ f₀.Coord (φ : B.Fn →+* Y.Fn) g₀ (A₁ * (A₀.map φ)⁻¹) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e B Y j f₀ S A₀ k S' φ f hT hR
  obtain ⟨A₁, hA₁⟩ := S'.nonempty (genericPoint Y.X)
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hA₁
  have hmapd : ∀ {A : Mat Dw.mult B.Fn}, (∀ τ, (A τ).det ≠ 0) →
      ∀ τ, (A.map (φ : B.Fn →+* Y.Fn) τ).det ≠ 0 := fun {A} hA τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hA τ)
  have hgen : genericPt Y ≫ f = spMap (φ : B.Fn →+* Y.Fn) ≫ genericPt B := hR.hom
  have hx : genericPt Y ≫ (f ≫ j) ≫ genι Z = spMap (φ : B.Fn →+* Y.Fn) ≫ genericPt B ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e Y = (φ : B.Fn →+* Y.Fn).comp (constF e B) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨g₀, hg₀⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) (φ : B.Fn →+* Y.Fn) inferInstance hst₀ hx hc).2
    (A₁ * (A₀.map (φ : B.Fn →+* Y.Fn))⁻¹) fun τ => by
      rw [Pi.mul_apply, Matrix.det_mul, Pi.inv_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact Ne.isUnit (mul_ne_zero (hA₁d τ) (inv_ne_zero (hmapd hA₀d τ)))
  refine ⟨g₀, A₁, ⟨hA₁, fun y A' hA' => ?_⟩, hg₀⟩
  obtain ⟨A, hA⟩ := S.nonempty (f y)
  obtain ⟨φ₁, fA, hfA⟩ := hT.2 (f y) A hA
  have hAd : ∀ τ, (A τ).det ≠ 0 := Fr.det_ne hA
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  let aY : Y.X.presheaf.stalk y →+* Y.Fn := algebraMap (Y.X.presheaf.stalk y) Y.X.functionField
  let aB : B.X.presheaf.stalk (f y) →+* B.Fn := algebraMap (B.X.presheaf.stalk (f y)) B.X.functionField
  let σ : B.X.presheaf.stalk (f y) →+* Y.X.presheaf.stalk y := (f.stalkMap y).hom
  have hcomp : (φ : B.Fn →+* Y.Fn).comp aB = aY.comp σ :=
    RingHom.ext fun a => map_algebraMap_stalk hR.hom y a
  obtain ⟨G, hG, hGd⟩ := exists_lift aY (IsFractionRing.injective (Y.X.presheaf.stalk y) Y.X.functionField)
    (fun x hx => mem_O_ratOf.1 hx) (hR.sub y A' hA' A hA)
  have hstA : fA.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ fA inferInstance
  have hσ : spMap σ ≫ stalkPt B (f y) = stalkPt Y y ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hx' : stalkPt Y y ≫ (f ≫ j) ≫ genι Z = spMap σ ≫ stalkPt B (f y) ≫ j ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, ← hσ, Category.assoc]
  obtain ⟨f', hf'⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA (Y.X.presheaf.stalk y) (σ.comp φ₁)
    (stalkPt Y y ≫ (f ≫ j) ≫ genι Z) σ inferInstance hstA hx' rfl).2 G hGd
  have hst' : f'.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f' inferInstance
  have haY : spMap aY ≫ stalkPt Y y = genericPt Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  have hx'' : genericPt Y ≫ (f ≫ j) ≫ genι Z = spMap aY ≫ stalkPt Y y ≫ (f ≫ j) ≫ genι Z := by
    rw [← haY, Category.assoc]
  have hc' : constF e Y = aY.comp (σ.comp φ₁) := by
    rw [← RingHom.comp_assoc, ← hcomp, RingHom.comp_assoc, hc, hfA.2.1]
  obtain ⟨T, hTc, -⟩ := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f' Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) aY inferInstance hst' hx'' hc').1 g₀).1
  have h1 := GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f' _ _ _ g₀ σ aY G T inferInstance hf' hTc
  have h2 := GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₀ _ _ _ g₀ aB (φ : B.Fn →+* Y.Fn) _ _
    inferInstance hfA hg₀
  rw [hcomp] at h2
  have hu := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA Y.Fn (constF e Y)
    (genericPt Y ≫ (f ≫ j) ≫ genι Z) (aY.comp σ) inferInstance hstA h1.1 h1.2.1).1 g₀).1.unique h1 h2
  have hG' : G.map aY = A' * (A.map (φ : B.Fn →+* Y.Fn))⁻¹ := hG
  rw [hG', Mat.map_mul, Mat.map_inv, ← mul_assoc, ← mul_assoc, mul_assoc A₁, Mat.inv_mul (hmapd hA₀d), mul_one] at hu
  have hT' : T = A₁ * A'⁻¹ := by
    have h3 := congrArg (fun M => M * A.map (φ : B.Fn →+* Y.Fn) * A'⁻¹) hu
    rwa [mul_assoc (T * A'), mul_assoc A₁, Mat.inv_mul (hmapd hAd), mul_one, mul_one, mul_assoc,
      Mat.mul_inv hA'd, mul_one] at h3
  exact ⟨σ.comp φ₁, f', hT' ▸ hTc⟩

end GlobalTheory.ShFam.TieUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedFramesParabolicRelation
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePairGram.Comb

theorem sum_shift {r p m : ℕ} (hm : p + m = r) (f : Fin r → ℂ) (h : ∀ c : Fin r, (c : ℕ) < p → f c = 0) :
    ∑ c, f c = ∑ i : Fin m, f ⟨p + i, by omega⟩ := by
  subst hm
  rw [Fin.sum_univ_add, Finset.sum_eq_zero (fun c _ => h _ (by simp)), zero_add]
  rfl

theorem sum_rev {r p : ℕ} (hp : p ≤ r) (f : Fin r → ℂ) (h : ∀ c : Fin r, p ≤ (c : ℕ) → f c = 0) :
    ∑ c, f c = ∑ i : Fin p, f ⟨p - 1 - i, by omega⟩ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [Fin.sum_univ_add, Finset.sum_eq_zero (s := Finset.univ) (f := fun i : Fin m => f (Fin.natAdd p i))
    (fun c _ => h _ (by simp)), add_zero, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  apply Fin.ext
  simp [Fin.val_rev]
  omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_comb (X : Data E r) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h1 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x τ)⁻¹ * mat x' τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x' τ)⁻¹ * mat x τ) a b = 0)
    (ρ : E →+* ℂ) (m : ℕ) (hm : ρ ∈ X.Ψ → m = r - X.p0) (hm' : ρ ∉ X.Ψ → m = X.p0)
    (v : Fin r → E) (b : ℕ) (hb : b < m) :
    Formalism.L2.PjFree.perFr X x' v ρ b = ∑ i : Fin m, coef X x x' ρ b i * Formalism.L2.PjFree.perFr X x v ρ i := by
  have hp := X.p0_le
  by_cases h : ρ ∈ X.Ψ
  · have hm := hm h
    have hd : IsUnit (mat x ⟨ρ, h⟩).det := (hx _).1.isUnit
    have hb' : X.p0 + b < r := by omega
    have e1 : Formalism.L2.PjFree.perFr X x' v ρ b = ∑ c : Fin r, ((mat x' ⟨ρ, h⟩)⁻¹ * mat x ⟨ρ, h⟩) ⟨_, hb'⟩ c *
        ((mat x ⟨ρ, h⟩)⁻¹.mulVec (Data.emb ρ v)) c := by
      unfold Formalism.L2.PjFree.perFr
      rw [dif_pos h, dif_pos hb']
      conv_lhs => rw [← mul_nonsing_inv_cancel_right (mat x ⟨ρ, h⟩) (mat x' ⟨ρ, h⟩)⁻¹ hd, ← mulVec_mulVec]
      rfl
    rw [e1, sum_shift (p := X.p0) (m := m) (by omega) _
      (fun c hc => by rw [h2 _ _ _ (Nat.le_add_right _ _) hc, zero_mul])]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : X.p0 + (i : ℕ) < r := by have := i.2; omega
    congr 1
    · simp only [coef, dif_pos h, ent]
      rw [dif_pos (And.intro hb' hi)]
    · unfold Formalism.L2.PjFree.perFr
      rw [dif_pos h, dif_pos hi]
  · obtain rfl := hm' h
    have h' : conjEmb ρ ∈ X.Ψ := by_contra fun h' => h ((X.cmType ρ).2 h')
    have hd : IsUnit (mat x ⟨_, h'⟩).det := (hx _).1.isUnit
    have hb' : X.p0 - 1 - b < r := by omega
    have e1 : Formalism.L2.PjFree.perFr X x' v ρ b = ∑ c : Fin r, ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) c ⟨_, hb'⟩ *
        hermC (conjEmb ρ) X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (mat x ⟨_, h'⟩) c) (Data.emb (conjEmb ρ) v) := by
      unfold Formalism.L2.PjFree.perFr
      rw [dif_neg h, dif_pos h', dif_pos hb']
      conv_lhs => rw [← mul_nonsing_inv_cancel_left (mat x ⟨_, h'⟩) (mat x' ⟨_, h'⟩) hd]
      generalize (mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩ = n
      change Matrix (Fin r) (Fin r) ℂ at n
      simp only [hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.sum_mul, Finset.mul_sum]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      simp only [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring
    rw [e1]
    refine Eq.trans (sum_rev hp _ fun c hc => ?_) ?_
    · rw [h1 _ _ _ hc (by simp only; omega), zero_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : X.p0 - 1 - (i : ℕ) < r := by omega
    have hi2 : (i : ℕ) < X.p0 := by have := i.2; omega
    congr 1
    · simp only [coef, dif_neg h, dif_pos h', ent]
      rw [dif_pos (And.intro hi hb')]
    · unfold Formalism.L2.PjFree.perFr
      rw [dif_neg h, dif_pos h', dif_pos hi]

def hmap {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) :
    (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z := fun j => ∑ i : Fin (μ (e j).1), C (e j).1 (e j).2 i * z (e.symm ⟨(e j).1, i⟩)
  map_add' z w := by
    funext j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a z := by
    funext j
    simp [Finset.mul_sum, mul_left_comm]

theorem hmap_apply {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) (z : Fin g → ℂ)
    (τ : T) (b : Fin (μ τ)) : hmap e C z (e.symm ⟨τ, b⟩) = ∑ i : Fin (μ τ), C τ b i * z (e.symm ⟨τ, i⟩) := by
  have key : ∀ s : Σ τ : T, Fin (μ τ), s = ⟨τ, b⟩ →
      ∑ i : Fin (μ s.1), C s.1 s.2 i * z (e.symm ⟨s.1, i⟩) = ∑ i : Fin (μ τ), C τ b i * z (e.symm ⟨τ, i⟩) := by
    rintro _ rfl
    rfl
  exact key _ (e.apply_symm_apply _)

theorem hmap_single {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) (τ : T)
    (i : Fin (μ τ)) : hmap e C (Pi.single (e.symm ⟨τ, i⟩) 1) =
      ∑ b : Fin (μ τ), C τ b i • (Pi.single (e.symm ⟨τ, b⟩) 1 : Fin g → ℂ) := by
  funext j
  obtain ⟨⟨τ', b'⟩, rfl⟩ := e.symm.surjective j
  rw [hmap_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hτ : τ' = τ
  · subst hτ
    have hs : ∀ a b : Fin (μ τ'), (Pi.single (e.symm ⟨τ', a⟩) (1 : ℂ) : Fin g → ℂ) (e.symm ⟨τ', b⟩) =
        if a = b then 1 else 0 := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simp
      · rw [if_neg hab, Pi.single_eq_of_ne (fun h => hab (by simpa using h.symm))]
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro c _
      rw [Pi.single_eq_of_ne (fun h => hτ (by simpa using congrArg Sigma.fst (e.symm.injective h))), mul_zero]
    · intro c _
      rw [Pi.single_eq_of_ne (fun h => hτ (by simpa using congrArg Sigma.fst (e.symm.injective h))), mul_zero]

theorem isDerivAt0_comp {g : ℕ} {X : Scheme.{0}} (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ z, e' (h z) = e z) {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hd : IsDerivAt0 e w v) : IsDerivAt0 e' (h w) v := by
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [hd.1, ← he 0, map_zero]
  · rw [hd.2 U hU f]
    let hc : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := h.toContinuousLinearEquiv
    have e1 : (fun z => valAt' (e z) U f) = (fun z => valAt' (e' z) U f) ∘ hc := by
      funext z
      simp only [Function.comp, hc, LinearEquiv.coe_toContinuousLinearEquiv', he]
    rw [e1, hc.comp_right_fderiv]
    simp [hc]

end GlobalTheory.FramePairGram.Comb


open GlobalTheory.FramePairGram.Comb in
theorem GlobalTheory.FramePairGram.lie_comb_of_block : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.IsUnf U → Formalism.L2.PjFree.GoodEmb c σ → ∀ (k : U.Comp) (x x' : (U.X k).dom), (∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x.1 τ)⁻¹ * mat x'.1 τ) a b = 0) → (∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x'.1 τ)⁻¹ * mat x.1 τ) a b = 0) → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), Formalism.L2.Pj.IsCombAt (U.un k x').x ((U.un k x').u τ) (fun b => (coef (U.X k) x.1 x'.1 (Formalism.L2.PjFree.relab c σ τ) b i : CAt σ)) ((U.un k x).u τ i) := by
  intro E _ _ _ r H Dw l Xo c σ U hU hσ k x x' h1 h2 τ i
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hF⟩ := hU
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hty k
  obtain ⟨P, hP, hper, hx, hu, -⟩ := hF k x
  obtain ⟨P', hP', hper', hx', hu', -⟩ := hF k x'
  obtain ⟨hEU, hEL, -, -⟩ := GlobalTheory.exp_four_clauses E H Dw l Xo c σ hσ g e F
  let C : (E →+* ℂ) → ℕ → ℕ → ℂ := fun τ b i => coef (U.X k) x.1 x'.1 (Formalism.L2.PjFree.relab c σ τ) b i
  have hL : ∀ a, P' a = hmap e C (P a) := fun a => funext fun j => by
    rw [hP', perFr_comb (U.X k) x.2 h1 h2 _ (Dw.mult (e j).1)
      (fun h => (if_pos ((hrt _).1 ((hty _).1 h))).trans (by omega))
      (fun h => (if_neg (fun h' => h ((hty _).2 ((hrt _).2 h')))).trans hp0.symm) _ _ (e j).2.2]
    simp only [hmap, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP, Equiv.apply_symm_apply]
  have hsurj : Function.Surjective (hmap e C) := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range P') := by rw [hper'.2.2.2.1]; trivial
    refine (Submodule.span_le (p := (LinearMap.range (hmap e C)).restrictScalars ℝ)).2 ?_ hy
    rintro _ ⟨a, rfl⟩
    exact ⟨P a, (hL a).symm⟩
  let hE : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.ofBijective (hmap e C) ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  have hex : ∀ z, (F.ex (ik k) P' (hE z)).left = (F.ex (ik k) P z).left :=
    hEU (ik k) P P' hper hper' (LinearEquiv.refl _ _) hE (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩)
      (fun a => ⟨0, by simp⟩) hL
  have hd := isDerivAt0_comp (fun z => (F.ex (ik k) P z).left) (fun z => (F.ex (ik k) P' z).left) hE hex (hu τ i)
  have hs : hE (Pi.single (e.symm ⟨τ, i⟩) 1) = ∑ b : Fin (Dw.mult τ), C τ b i • (Pi.single (e.symm ⟨τ, b⟩) 1 : Fin g → ℂ) :=
    hmap_single e C τ i
  rw [hs] at hd
  rw [hx']
  exact hEL (ik k) P' hper' _ (fun b => Pi.single (e.symm ⟨τ, b⟩) 1) ((U.un k x').u τ) _ _ (fun b => hu' τ b) hd

end
end

