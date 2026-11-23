module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarDecompositionIndefiniteUnitary
section
open scoped Matrix
open Formalism.BasicNotions.TH

namespace GlobalTheory.UnitaryPolar

open Matrix
open scoped MatrixOrder ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem root {S A : Matrix ι ι ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hA : A.PosSemidef)
    (h : A * S * A = S) : ∃ R : Matrix ι ι ℂ, R.PosSemidef ∧ R * R = A ∧ R * S * R = S := by
  obtain ⟨R, hR, hRR, hu⟩ : ∃ R : Matrix ι ι ℂ, R.PosSemidef ∧ R * R = A ∧
      ∀ T : Matrix ι ι ℂ, T.PosSemidef → T * T = A → R = T :=
    ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      fun T hT e => CFC.sqrt_unique e hT.nonneg⟩
  have a1 : R * (R * (S * A * S)) = 1 := by
    rw [← Matrix.mul_assoc, hRR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, h1]
  have a2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (Matrix.isUnit_det_of_right_inverse a1)
  have a3 : R⁻¹ * R⁻¹ = S * A * S := by
    calc R⁻¹ * R⁻¹ = R⁻¹ * R⁻¹ * (R * (R * (S * A * S))) := by rw [a1, Matrix.mul_one]
      _ = R⁻¹ * (R⁻¹ * R) * R * (S * A * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [a2, Matrix.mul_one, a2, Matrix.one_mul]
  have a4 : R = S * R⁻¹ * S := by
    refine hu _ ?_ ?_
    · have := hR.inv.conjTranspose_mul_mul_same S
      rwa [h2] at this
    · calc S * R⁻¹ * S * (S * R⁻¹ * S) = S * (R⁻¹ * (S * S) * R⁻¹) * S := by simp only [Matrix.mul_assoc]
        _ = (S * S) * A * (S * S) := by rw [h1, Matrix.mul_one, a3, ← h1]; simp only [Matrix.mul_assoc]
        _ = A := by rw [h1, Matrix.mul_one, Matrix.one_mul]
  refine ⟨R, hR, hRR, ?_⟩
  calc R * S * R = S * R⁻¹ * S * S * R := by rw [← a4]
    _ = S * (R⁻¹ * (S * S) * R) := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h1, Matrix.mul_one, a2, Matrix.mul_one]

theorem polar_inv {S U : Matrix ι ι ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hU : Uᴴ * S * U = S) :
    ∃ K Q : Matrix ι ι ℂ, Kᴴ * S * K = S ∧ S * K = K * S ∧ Qᴴ * S * Q = S ∧ S * Q * S * Q = 1 ∧
      U = K * Q * Q := by
  have hS : ∀ X : Matrix ι ι ℂ, S * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b1 : (S * Uᴴ * S) * U = 1 := by
    rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hU, h1]
  have b2 : U * S * Uᴴ = S := by
    have := congrArg (· * S) (mul_eq_one_comm.1 b1)
    simpa only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨P, hP, hPP, hPS⟩ := root h1 h2 (Matrix.posSemidef_conjTranspose_mul_self U) (by
    calc Uᴴ * U * S * (Uᴴ * U) = Uᴴ * (U * S * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = S := by rw [b2, hU])
  obtain ⟨Q, hQ, hQQ, hQS⟩ := root h1 h2 hP hPS
  have hP' : ∀ X : Matrix ι ι ℂ, P * (S * (P * X)) = S * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPS]
  have c0 : (U * (S * P * S))ᴴ = S * P * S * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, h2, hP.isHermitian.eq, Matrix.mul_assoc]
  have c1 : (U * (S * P * S))ᴴ * S * (U * (S * P * S)) = S := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * S * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hU]; simp only [Matrix.mul_assoc, hS, hP']
  have c2 : (U * (S * P * S))ᴴ * (U * (S * P * S)) = 1 := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hPP]; simp only [Matrix.mul_assoc, hS, hP', h1]
  refine ⟨U * (S * P * S), Q, c1, ?_, by rw [hQ.isHermitian.eq, hQS], ?_, ?_⟩
  · generalize U * (S * P * S) = K at c1 c2
    calc S * K = (K * Kᴴ) * S * K := by rw [mul_eq_one_comm.1 c2, Matrix.one_mul]
      _ = K * (Kᴴ * S * K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [c1]
  · rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hQS, h1]
  · rw [Matrix.mul_assoc _ Q, hQQ, Matrix.mul_assoc, Matrix.mul_assoc S, Matrix.mul_assoc S, hPS, h1, Matrix.mul_one]

theorem jm_mul_self (R S : ℕ) : Jm R S * Jm R S = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem jm_conjTranspose (R S : ℕ) : (Jm R S)ᴴ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem polar (R S : ℕ) (u : Mat R S) (hu : uᴴ * Jm R S * u = Jm R S) :
    ∃ k q : Mat R S, kᴴ * Jm R S * k = Jm R S ∧
      Jm R S * k = k * Jm R S ∧ qᴴ * Jm R S * q = Jm R S ∧ Jm R S * q * Jm R S * q = 1 ∧ u = k * q * q :=
  polar_inv (jm_mul_self R S) (jm_conjTranspose R S) hu

end GlobalTheory.UnitaryPolar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionTorusAndAbelianQuotient
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.SemiAbAct

theorem exists_torus_quotient_act : ∀ (O : Type) [CommRing O] (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (act : OAct O G), IsSemiAbelian G → ∀ (T : TorusExtension G), letI := T.addCommGroup; letI := T.grpB; ∃ (actB : OAct O T.B) (actT : OAct O (splitTorus (Sp k) T.X)), (∀ a, T.q ≫ actB.act a = act.act a ≫ T.q) ∧ (∀ a, actT.act a ≫ T.i = T.i ≫ act.act a) := by
  intro O _ k _ _ G _ act _ T
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.finite
  have := T.i_hom
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have := T.isAbelian.proper
  have hmono : Mono T.i := T.isKernel.flip.mono_snd_of_mono
  have hepi : Epi T.q := GlobalTheory.SemiRigid.epi_of_fpqc T.q
  have hA : ∀ a, IsMonHom (act.act a) := act.hom

  have hT : ∀ a, T.i ≫ act.act a ≫ T.q = toUnit _ ≫ η := by
    intro a
    rw [GlobalTheory.SemiRigid.torus_const T.X T.B (T.i ≫ act.act a ≫ T.q)]
    simp [IsMonHom.one_hom_assoc, IsMonHom.one_hom]
  let fT : ∀ a, splitTorus (Sp k) T.X ⟶ splitTorus (Sp k) T.X := fun a ↦
    T.isKernel.lift (T.i ≫ act.act a) (toUnit _) (by rw [Category.assoc, hT])
  have hfT : ∀ a, fT a ≫ T.i = T.i ≫ act.act a := fun a ↦ T.isKernel.lift_fst _ _ _

  have hB : ∀ a, ∃ g, T.q ≫ g = act.act a ≫ T.q := fun a ↦
    GlobalTheory.SemiRigid.exists_desc T.q (act.act a ≫ T.q) fun Z x y h ↦ by
      obtain ⟨τ, hτ⟩ := GlobalTheory.SemiRigid.exists_eq_mul T.isKernel h
      rw [hτ, MonObj.mul_comp_assoc, MonObj.mul_comp, Category.assoc, Category.assoc, hT,
        comp_toUnit_assoc, ← Hom.one_def, _root_.one_mul, Category.assoc]
  choose fB hfB using hB
  have hmulT : ∀ a, IsMonHom (fT a) := fun a ↦ by
    refine ⟨?_, ?_⟩
    · rw [← cancel_mono T.i, Category.assoc, hfT, IsMonHom.one_hom_assoc, IsMonHom.one_hom,
        IsMonHom.one_hom]
    · rw [← cancel_mono T.i, Category.assoc, hfT, IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
        Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hfT]
  have hmulB : ∀ a, IsMonHom (fB a) := fun a ↦ by
    refine ⟨?_, ?_⟩
    · have h := IsMonHom.one_hom (f := T.q)
      rw [← h, Category.assoc, hfB, IsMonHom.one_hom_assoc, h]
    · have hqq : Epi (T.q ⊗ₘ T.q) := by
        have : Epi (T.q ▷ G) := GlobalTheory.SemiRigid.epi_of_fpqc _
        have : Epi (T.q ▷ T.B) := GlobalTheory.SemiRigid.epi_of_fpqc _
        have : Epi (lift (snd T.B G) (fst T.B G)) :=
          epi_of_epi_fac (h := 𝟙 _) (f := lift (snd G T.B) (fst G T.B)) (by apply CartesianMonoidalCategory.hom_ext <;> simp)
        have : Epi (lift (snd T.B T.B) (fst T.B T.B)) :=
          epi_of_epi_fac (h := 𝟙 _) (f := lift (snd T.B T.B) (fst T.B T.B)) (by apply CartesianMonoidalCategory.hom_ext <;> simp)
        have hs : T.B ◁ T.q =
            lift (snd T.B G) (fst T.B G) ≫ (T.q ▷ T.B) ≫ lift (snd T.B T.B) (fst T.B T.B) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [MonoidalCategory.tensorHom_def, hs]
        infer_instance
      rw [← cancel_epi (T.q ⊗ₘ T.q), ← IsMonHom.mul_hom_assoc, hfB, IsMonHom.mul_hom_assoc,
        IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, hfB]
  refine ⟨⟨fB, hmulB, ?_, ?_, ?_⟩, ⟨fT, hmulT, ?_, ?_, ?_⟩, hfB, hfT⟩
  · rw [← cancel_epi T.q, hfB, act.one, Category.comp_id, Category.id_comp]
  · intro a b
    rw [← cancel_epi T.q, hfB, act.mul, Category.assoc, ← hfB, reassoc_of% hfB]
  · intro a b
    rw [← cancel_epi T.q, hfB, MonObj.comp_mul, hfB, hfB, act.add, MonObj.mul_comp]
  · rw [← cancel_mono T.i, hfT, act.one, Category.comp_id, Category.id_comp]
  · intro a b
    rw [← cancel_mono T.i, hfT, act.mul, Category.assoc, hfT, reassoc_of% hfT]
  · intro a b
    rw [← cancel_mono T.i, hfT, MonObj.mul_comp, hfT, hfT, act.add, MonObj.comp_mul]

end GlobalTheory.SemiAbAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianIdentityComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

variable {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] (j : G₀ ⟶ G)

abbrev RangeIsId : Prop := ∀ x : G.left, x ∈ Set.range j.left ↔
  x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))

include j in
theorem unit_mem_fibre (s : S) : (η[G]).left s ∈ G.hom ⁻¹' {s} := by
  show G.hom ((η[G]).left s) = s
  rw [← Scheme.Hom.comp_apply, Over.w]
  rfl

theorem isConnected_fibre [IsOpenImmersion j.left] (hr : RangeIsId j) (s : S) :
    _root_.IsConnected (G₀.hom ⁻¹' {s}) := by
  have hw : ∀ x, G.hom (j.left x) = G₀.hom x := fun x => by
    rw [← Scheme.Hom.comp_apply, Over.w]
  have himg : j.left '' (G₀.hom ⁻¹' {s}) = connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := (hr (j.left x)).1 ⟨x, rfl⟩
      rwa [hw, show G₀.hom x = s from hx] at this
    · intro hy
      have hys : G.hom y = s := connectedComponentIn_subset (G.hom ⁻¹' {s}) _ hy
      obtain ⟨x, rfl⟩ := (hr y).2 (by rwa [hys])
      exact ⟨x, by rw [Set.mem_preimage, ← hw, hys]; rfl, rfl⟩
  have hc : _root_.IsConnected (connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s)) :=
    isConnected_connectedComponentIn_iff.mpr (unit_mem_fibre j s)
  rw [← himg] at hc
  exact ⟨hc.nonempty.of_image, j.left.isOpenEmbedding.isInducing.isPreconnected_image.1 hc.isPreconnected⟩

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingExtensionOfRel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory

theorem exists_separating_extension_of_rel : ∀ {α β L : Type} [Infinite L] (S : Finset (α → L)) (r : β → α) (Rel : (α → L) → (β → L) → Prop), Function.Injective r → (∀ e ∈ S, ∀ e' ∈ S, ∀ f f', Rel e f → Rel e' f' → (e ∘ r = e' ∘ r ↔ f = f')) → ∃ tr : (α → L) → α → L, (∀ e ∈ S, ∀ f, Rel e f → ∀ k, f k = tr e (r k)) ∧ ∀ e ∈ S, ∀ e' ∈ S, (∃ k, e (r k) ≠ e' (r k)) → ∃ k, tr e (r k) ≠ tr e' (r k) := by
  intro α β L _ S r Rel hr H
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · exact ⟨id, fun _ _ _ _ k => isEmptyElim k, fun _ _ _ _ h => h⟩
  have hF : (⋃ e ∈ (S : Set (α → L)), {f | Rel e f}).Finite := by
    refine Set.Finite.biUnion S.finite_toSet fun e he => Set.Subsingleton.finite ?_
    intro f hf f' hf'
    exact (H e he e he f f' hf hf').1 rfl
  have hinf := hF.infinite_compl
  have hT : ((fun e : α → L => e ∘ r) '' (S : Set (α → L))).Countable :=
    (S.finite_toSet.image _).countable
  obtain ⟨n, hn⟩ := Set.countable_iff_exists_injOn.1 hT
  let j : (β → L) → (β → L) := fun c => (hinf.natEmbedding _ (n c)).1
  have hj : ∀ c, ∀ e ∈ S, ¬ Rel e (j c) := by
    intro c e he h
    exact (hinf.natEmbedding _ (n c)).2 (Set.mem_biUnion (Finset.mem_coe.2 he) h)
  have hji : ∀ e ∈ S, ∀ e' ∈ S, j (e ∘ r) = j (e' ∘ r) → e ∘ r = e' ∘ r := by
    intro e he e' he' h
    exact hn ⟨e, he, rfl⟩ ⟨e', he', rfl⟩ ((hinf.natEmbedding _).injective (Subtype.ext h))
  let g : (β → L) → (β → L) := fun c =>
    if h : ∃ f, ∃ e ∈ S, e ∘ r = c ∧ Rel e f then h.choose else j c
  have hg : ∀ c, (∃ e ∈ S, e ∘ r = c ∧ Rel e (g c)) ∨ g c = j c := by
    intro c
    by_cases h : ∃ f, ∃ e ∈ S, e ∘ r = c ∧ Rel e f
    · left
      have : g c = h.choose := dif_pos h
      rw [this]
      exact h.choose_spec
    · exact Or.inr (dif_neg h)
  refine ⟨fun e => Function.extend r (g (e ∘ r)) e, ?_, ?_⟩
  · intro e he f hf k
    have h : ∃ f, ∃ e' ∈ S, e' ∘ r = e ∘ r ∧ Rel e' f := ⟨f, e, he, rfl, hf⟩
    have h1 : g (e ∘ r) = h.choose := dif_pos h
    obtain ⟨e', he', h2, h3⟩ := h.choose_spec
    have h4 := (H e' he' e he _ _ h3 hf).1 h2
    show f k = Function.extend r (g (e ∘ r)) e (r k)
    rw [hr.extend_apply, h1, h4]
  · rintro e he e' he' ⟨k, hk⟩
    by_contra hc
    have hge : g (e ∘ r) = g (e' ∘ r) := by
      funext i
      by_contra hi
      refine hc ⟨i, ?_⟩
      show Function.extend r (g (e ∘ r)) e (r i) ≠ Function.extend r (g (e' ∘ r)) e' (r i)
      rwa [hr.extend_apply, hr.extend_apply]
    apply hk
    suffices h : e ∘ r = e' ∘ r from congrFun h k
    rcases hg (e ∘ r) with ⟨a, ha, h1, h2⟩ | h1 <;> rcases hg (e' ∘ r) with ⟨b, hb, h3, h4⟩ | h3
    · rw [← h1, ← h3]
      exact (H a ha b hb _ _ h2 h4).2 hge
    · exact absurd (by rw [← h3, ← hge]; exact h2) (hj (e' ∘ r) a ha)
    · exact absurd (by rw [← h1, hge]; exact h4) (hj (e ∘ r) b hb)
    · exact hji e he e' he' (by rw [← h1, ← h3, hge])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtFixedNearOneCommutativeCentralizerStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqrt_fixed_near_one_commutative_centralizer : ∀ (p : ℕ) [Fact p.Prime] (v : AwayP p) (B : Type) [Ring B] [Algebra (Qv v) B] [Module.Finite (Qv v) B], letI : TopologicalSpace B := moduleTopology (Qv v) B; ∀ (e : B) (σ : B →ₗ[Qv v] B), (∀ a b : B, a * e = e * a → b * e = e * b → a * b = b * a) → (∀ a : B, a * e = e * a → σ a * e = e * σ a) → (∀ a b : B, a * e = e * a → b * e = e * b → σ (a * b) = σ a * σ b) → σ 1 = 1 → ∃ W ∈ nhds (1 : B), ∀ s ∈ W, s * e = e * s → σ s = s → ∃ r : B, r * e = e * r ∧ σ r = r ∧ r * r = s := by
  first | (exact @GlobalTheory.sqrt_fix_near_one_centralizer) | (exact GlobalTheory.sqrt_fix_near_one_centralizer) | (intros; apply GlobalTheory.sqrt_fix_near_one_centralizer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSumTwoSidedMulEqMatrixUnitUnitaryDatumStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_two_sided_mul_eq_matrixUnit_unitaryDatum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (r : ℕ) (e : Fin r → G.C),
    (∀ x : G.C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) → ∀ i i' : Fin r,
    ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → G.C), ∀ β : Fin r → L,
      ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i := by
  first | (exact @GlobalTheory.exists_sum_mul_mul_eq_matrixUnit_htGroup) | (exact GlobalTheory.exists_sum_mul_mul_eq_matrixUnit_htGroup) | (intros; apply GlobalTheory.exists_sum_mul_mul_eq_matrixUnit_htGroup  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieOfIndefiniteUnitaryLieRightAc
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

namespace GlobalTheory.RealLift.SpLie

open Matrix

def sgnD {p q : ℕ} : Ix p q → ℂ
  | .inl _ => 1
  | .inr _ => -1

theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal sgnD := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, sgnD, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem lineSign_eq_mul {p q r s : ℕ} (a : Ix p q) (b : Ix r s) : lineSign a b = sgnD a * sgnD b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign, sgnD]

theorem upq_entry {r s : ℕ} {Y : Mat r s} (hY : Y ∈ upq r s) (b k : Ix r s) :
    star (Y k b) * sgnD k + sgnD b * Y b k = 0 := by
  have h : (Yᴴ * Jm r s + Jm r s * Y) b k = 0 := by
    rw [show Yᴴ * Jm r s + Jm r s * Y = 0 from hY]; rfl
  rw [Jm_eq_diagonal] at h
  simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h

theorem sympl_eq_dot {l : Type} [Fintype l] [DecidableEq l] (u v : l ⊕ l → ℝ) :
    sympl u v = -(u ⬝ᵥ (Matrix.J l ℝ *ᵥ v)) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, ite_mul, Finset.sum_ite_eq]
  simp only [mul_comm (v _)]
  ring

theorem sum_zero {P Q R S : ℕ} (c c' : Matrix (Ix P Q) (Ix R S) ℂ) (Y : Mat R S) (hY : Y ∈ upq R S) :
    (∑ a, ∑ b, lineSign a b * (c * Yᵀ) a b * star (c' a b)) +
      ∑ a, ∑ b, lineSign a b * c a b * star ((c' * Yᵀ) a b) = 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  have e1 : ∀ b, lineSign a b * (c * Yᵀ) a b * star (c' a b) =
      ∑ k, sgnD a * c a k * star (c' a b) * (sgnD b * Y b k) := by
    intro b
    rw [lineSign_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply]; ring
  have e2 : ∀ b, lineSign a b * c a b * star ((c' * Yᵀ) a b) =
      ∑ k, sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k)) := by
    intro b
    rw [lineSign_eq_mul, Matrix.mul_apply, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply, star_mul']; ring
  simp only [e1, e2]
  rw [Finset.sum_comm (f := fun b k => sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k))),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  linear_combination (sgnD a * c a k * star (c' a b)) * upq_entry hY b k

theorem mem_sp_of_sympl {l : Type} [Fintype l] [DecidableEq l] (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ u v, sympl (Z *ᵥ u) v + sympl u (Z *ᵥ v) = 0) : Z ∈ LieAlgebra.Symplectic.sp l ℝ := by
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  show Zᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -Z
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  rw [sympl_eq_dot, sympl_eq_dot] at h1
  simp [mulVec, dotProduct, Pi.single_apply, Matrix.mul_apply] at h1 ⊢
  linarith

theorem exists_sp_rightAct : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ Y hY
  let G : (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ) :=
    { toFun := fun c w => c w * (Y w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  set Z := LinearMap.toMatrix' (φ.toLinearMap ∘ₗ G ∘ₗ φ.symm.toLinearMap) with hZdef
  have hZ : ∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ := by
    intro c; rw [hZdef, LinearMap.toMatrix'_mulVec]; simp [G]
  refine ⟨Z, ?_, hZ, ?_⟩
  · refine mem_sp_of_sympl Z fun u v => ?_
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    have hs : (∑ w, ∑ a, ∑ b, lineSign a b * (c w * (Y w)ᵀ) a b * star (c' w a b)) +
        (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star ((c' w * (Y w)ᵀ) a b)) = 0 := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun w _ => sum_zero _ _ _ (hY w)
    rw [hZ, hZ, hφ, hφ, ← mul_add, ← Complex.add_im]
    simp only [hs, Complex.zero_im, mul_zero]
  · intro t c
    have hpow : ∀ (n : ℕ) (c : ι → Matrix (Ix P Q) (Ix R S) ℂ),
        (t • Z) ^ n *ᵥ φ c = φ fun w => c w * ((t • Y w) ^ n)ᵀ := by
      intro n
      induction n with
      | zero => intro c; simp
      | succ n ih =>
        intro c
        rw [pow_succ, ← mulVec_mulVec, Matrix.smul_mulVec, hZ, ← φ.map_smul]
        have : (t • fun w => c w * (Y w)ᵀ) = fun w => c w * (t • Y w)ᵀ := by
          funext w; simp [Matrix.transpose_smul, Matrix.mul_smul]
        rw [this, ih]
        congr 1; funext w
        rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc]
    letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
    letI : NormedRing (Mat R S) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Mat R S) := Matrix.linftyOpNormedAlgebra
    have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • (t • Z) ^ n) *ᵥ φ c)
        (NormedSpace.exp (t • Z) *ᵥ φ c) :=
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Z)).map
        (Matrix.mulVec.addMonoidHomLeft (φ c)) (Continuous.matrix_mulVec continuous_id continuous_const)
    have hw : ∀ w, HasSum (fun n : ℕ => c w * (((n.factorial : ℝ)⁻¹ • (t • Y w) ^ n))ᵀ)
        (c w * (NormedSpace.exp (t • Y w))ᵀ) := by
      intro w
      have := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Y w)).matrix_transpose
      exact this.map (AddMonoidHom.mk' (fun M => c w * M) fun _ _ => Matrix.mul_add _ _ _)
        (continuous_const.matrix_mul continuous_id)
    have h2 := (Pi.hasSum.2 hw).map φ (LinearMap.continuous_of_finiteDimensional φ.toLinearMap)
    refine h1.unique ?_
    convert h2 using 1
    funext n
    rw [Matrix.smul_mulVec, hpow, ← φ.map_smul]
    congr 1; funext w
    simp [Matrix.transpose_smul, Matrix.mul_smul]

end GlobalTheory.RealLift.SpLie
end

