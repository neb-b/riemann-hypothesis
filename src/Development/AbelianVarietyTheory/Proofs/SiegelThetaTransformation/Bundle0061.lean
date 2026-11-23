module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestRingInjective
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.BorelDescent

theorem exists_testRing_injective {K : Type} [Field K] {S : Type} [Field S] [Algebra K S] (p q : TRing K)
    (φ : p.R →ₐ[K] S) (ψ : q.R →ₐ[K] S) (s : Set S) (hs : s.Finite) :
    ∃ (r : TRing K) (α : p.R →ₐ[K] r.R) (β : q.R →ₐ[K] r.R) (χ : r.R →ₐ[K] S),
      Function.Injective χ ∧ χ.comp α = φ ∧ χ.comp β = ψ ∧ ∀ a ∈ s, ∃ b, χ b = a := by
  obtain ⟨h1, h2⟩ := GlobalTheory.reduced_finiteType_iff_testRing K
  have hp := (h2 p).1
  have hq := (h2 q).1
  let R : Subalgebra K S := (φ.range ⊔ ψ.range) ⊔ Algebra.adjoin K s
  have hφ : φ.range.FG := by
    rw [← Algebra.map_top]; exact Algebra.FiniteType.out.map _
  have hψ : ψ.range.FG := by
    rw [← Algebra.map_top]; exact Algebra.FiniteType.out.map _
  have hR : R.FG := (hφ.sup hψ).sup (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  have hft : Algebra.FiniteType K R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨r, ⟨e⟩⟩ := h1 R hft inferInstance
  have m1 : ∀ x, φ x ∈ R := fun x =>
    (le_sup_left.trans le_sup_left : φ.range ≤ R) ⟨x, rfl⟩
  have m2 : ∀ x, ψ x ∈ R := fun x =>
    (le_sup_right.trans le_sup_left : ψ.range ≤ R) ⟨x, rfl⟩
  refine ⟨r, (e.symm : R →ₐ[K] r.R).comp (φ.codRestrict R m1), (e.symm : R →ₐ[K] r.R).comp (ψ.codRestrict R m2),
    R.val.comp (e : r.R →ₐ[K] R), Subtype.val_injective.comp e.injective, ?_, ?_, fun a ha => ?_⟩
  · ext x; simp
  · ext x; simp
  · exact ⟨e.symm ⟨a, (le_sup_right : Algebra.adjoin K s ≤ R) (Algebra.subset_adjoin ha)⟩, by simp⟩

theorem point_eq_of_injective {o R S : Type} [CommRing o] [CommRing R] [IsReduced R] [CommRing S] {X : Scheme.{0}}
    {f : X ⟶ Sp o} (h : IsQProjOver f) (j : R →+* S) (hj : Function.Injective j) (x x' : Sp R ⟶ X)
    (h₁ : x ≫ f = x' ≫ f) (h₂ : spMap j ≫ x = spMap j ≫ x') : x = x' := by
  have hsep : IsSeparated f := by
    obtain ⟨N, i, hi, -, rfl⟩ := h
    have : IsSeparated (PSpace.str o N) := by
      unfold PSpace.str
      infer_instance
    infer_instance
  have : IsDominant (spMap j) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  exact ext_of_isDominant_of_isSeparated (X := Sp R) f h₁ (spMap j) h₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem borDesc (Xo : Moduli Dw l) (c : Coeff l) : BorDesc Xo c := by
  classical
  intro S _ _ t y y' hb p q φ ψ yp yq hp hq
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨g, hg0, hgd, hchg⟩ := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).1 hb
  let s : Set S := (Set.range fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ)) => g k.1 k.2.1 k.2.2) ∪
    ((Set.range fun i => (t i : S)) ∪ Set.range fun i => ((t i)⁻¹ : Sˣ).val)
  have hs : s.Finite := (Set.finite_range _).union ((Set.finite_range _).union (Set.finite_range _))
  obtain ⟨r, α, β, χ, hχ, hα, hβ, hl⟩ := exists_testRing_injective p q φ ψ s hs
  have hred : IsReduced r.R := ((GlobalTheory.reduced_finiteType_iff_testRing c.F).2 r).2
  choose g₀ hg₀ using fun τ i j => hl (g τ i j) (Or.inl ⟨⟨τ, i, j⟩, rfl⟩)
  choose a ha using fun i => hl (t i : S) (Or.inr (Or.inl ⟨i, rfl⟩))
  choose b hb' using fun i => hl ((t i)⁻¹ : Sˣ).val (Or.inr (Or.inr ⟨i, rfl⟩))
  have hab : ∀ i, a i * b i = 1 := fun i => hχ (by rw [map_mul, ha, hb', map_one, Units.mul_inv])
  let t₀ : Ix Dw → (r.R)ˣ := fun i => ⟨a i, b i, hab i, (mul_comm _ _).trans (hab i)⟩
  let G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) r.R := fun τ => Matrix.of (g₀ τ)
  have hG0 : ∀ τ i j, i < j → G τ i j = 0 := fun τ i j hij =>
    hχ ((hg₀ τ i j).trans ((hg0 τ i j hij).trans (map_zero χ).symm))
  have hGd : ∀ τ i, G τ i i = (t₀ (some ⟨τ, i⟩) : r.R) := fun τ i =>
    hχ ((hg₀ τ i i).trans ((hgd τ i).trans (ha _).symm))
  have hdet : ∀ τ, IsUnit (G τ).det := fun τ => by
    have hlow : (G τ).IsLowerTriangular := fun i j hij => hG0 τ i j hij
    rw [Matrix.det_of_isLowerTriangular _ hlow, IsUnit.prod_univ_iff]
    intro i
    rw [hGd]
    exact Units.isUnit _
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ α yp
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ β yq
  have hzy : FrMap χ z y := frMap_cancel _ _ _ α χ yp z y hz (hα ▸ hp)
  have hzy' : FrMap χ z' y' := frMap_cancel _ _ _ β χ yq z' y' hz' (hβ ▸ hq)
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c r.R z G (t₀ none) hdet
  have hGg : (fun τ => (G τ).map χ) = g := funext fun τ => Matrix.ext fun i j => hg₀ τ i j
  have hwy : FrMap χ w y' := by
    rw [GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c _ _ χ z w y y' G _ hw hzy, hGg]
    have : χ (t₀ none : r.R) = (t none : S) := ha none
    rw [this]
    exact hchg
  have hx : z'.x = w.x := point_eq_of_injective Xo.qproj χ.toRingHom hχ _ _ (z'.x_over.trans w.x_over.symm)
    (hzy'.1.symm.trans hwy.1)
  have hwz : w = z' := GlobalTheory.Frames.frPt_eq_of_frMap_injective hS E H Dw l Xo c _ _ χ w z' y' hχ hx hwy hzy'
  subst hwz
  exact ⟨r, α, β, χ, z, w, t₀, hα, hβ, hz, hz',
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c r.R z w w).1 t₀).2 ⟨G, hG0, hGd, hw⟩, ha⟩

end GlobalTheory.BorelDescent


open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn in
theorem GlobalTheory.borDesc_and_wtField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), BorDesc Xo c ∧ WtField Xo c :=
  fun _ _ _ _ _ _ _ Xo c => ⟨GlobalTheory.BorelDescent.borDesc Xo c, wtField_of (GlobalTheory.BorelDescent.borDesc Xo c)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitCOfFiniteCharacter
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem unitC_of_finite_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cls : Type) [CommGroup Cls] [Finite Cls] (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), 1 ≤ Dw.p + Dw.q → CMP Xo c d _ Cls δ gdet false → UnitC d := by
  intro E _ _ _ H Dw l Xo c n d Cls _ _ δ gdet hpq hC
  have hSB := (@GlobalTheory.lawsFieldsSeparately).2.1
  have hAT := @_root_.GlobalTheory.Frames.allTest_of_secBaseChange hSB E _ _ _ H Dw d.l₂ d.Xo₂ d.c₂
  have hW := (GlobalTheory.Frames.algebraic_laws hSB E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
  obtain ⟨hs, hv⟩ := hC
  unfold Formalism.L2.Pj.sec Formalism.L2.Pj.secW at hs
  have hN := (show _ ∧ _ from hs).1
  have hm : Nat.card Cls ≠ 0 := Nat.card_pos.ne'

  have key : ∀ (p : Formalism.L2.Pj.TRing d.c₂.F) (y₀ : FrPt d.Xo₂ d.c₂ p.R),
      (d.cδ p y₀) ^ Nat.card Cls = 1 := by
    intro p y₀
    refine sub_eq_zero.mp (Formalism.L2.Pj.eq_zero_of_cpts d.c₂.F.val.toRingHom p _ fun ψ => ?_)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hSB E H Dw d.l₂ d.Xo₂ d.c₂ p.R
      (Formalism.L2.Pj.CAt d.c₂.F.val.toRingHom) ψ y₀
    have hev : Formalism.L2.Pj.evR d.Xo₂ d.c₂ d.cδ z = ψ (d.cδ p y₀) := by
      unfold Formalism.L2.Pj.evR Formalism.L2.Pj.evalAt
      split
      · next h => exact hW d.cδ hN _ _ _ _ _ _ _ _ h.choose_spec.choose_spec.choose_spec hz
      · next h => exact absurd ⟨p, ψ, y₀, hz⟩ h
    rw [map_sub, map_pow, map_one, ← hev, hv z]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, map_one,
      sub_self]
  unfold GlobalTheory.Dict.UnitC
  intro A y
  letI := A
  obtain ⟨p, φ, y₀, hy⟩ := hAT ℂ y
  have hev : Formalism.L2.Pj.evR d.Xo₂ d.c₂ d.cδ y = φ (d.cδ p y₀) := by
    unfold Formalism.L2.Pj.evR Formalism.L2.Pj.evalAt
    split
    · next h => exact hW d.cδ hN _ _ _ _ _ _ _ _ h.choose_spec.choose_spec.choose_spec hy
    · next h => exact absurd ⟨p, φ, y₀, hy⟩ h
  rw [hev]
  exact norm_eq_one_of_pow_eq_one (by rw [← map_pow, key, map_one]) hm

end GlobalTheory.Dict
end

