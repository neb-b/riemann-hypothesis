module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TorusConjugateCornerEntryEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem linked_iff_torus_conjugate {H K : Type} [Group H] [Field K] {r r' : H →* M4 K} {t : Kˣ × Kˣ}
    (h : ∀ g, r g = tconj t (r' g)) (i j : Fin 4) : Ge r i j ↔ Ge r' i j := by
  unfold Ge
  refine exists_congr fun g => ?_
  rw [h g]
  simp [tconj]

private theorem torus_conjugate_corner_entry_eq {H K : Type} [Group H] [Field K] {r r' : H →* M4 K} {t : Kˣ × Kˣ}
    (h : ∀ g, r g = tconj t (r' g)) (g : H) : r g 0 0 = r' g 0 0 := by
  rw [h g]
  simp [tconj, wv, wt]

private theorem diagonal_type_corner_cases {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hS : SoV Ω l) (hF : D.Fin0)
    (ξ : M.SS →ₐ[c.O] PadicAlgCl l) (hd : DiagType (M.rep ξ)) :
    (M.rep ξ D.s0 0 0 = ((D.th D.s0 : c.O) : PadicAlgCl l) ∧ NegZero M.gr (ξ.comp M.toSS)) ∨
    (M.rep ξ D.s0 0 0 = ((D.al D.s0 : c.O) : PadicAlgCl l) ∧ PosZero M.gr (ξ.comp M.toSS)) := by
  obtain ⟨t, r, hr, h⟩ := ptScale D hD M hF ξ
  obtain ⟨s1, s2, -⟩ := signs D hD M hF ξ
  have hd' : DiagType r := fun i j hij a b => hd i j hij ((linked_iff_torus_conjugate h i j).1 a) ((linked_iff_torus_conjugate h j i).1 b)
  have hs : (D.s0 : G ℚ Ω) ∈ D.Ip l := hD.decompSigma_mem.1.1
  rcases diagCases D hD hS r hr hd' with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨(torus_conjugate_corner_entry_eq h _).symm.trans (a _ hs), s1 fun i j hij e => b i j hij ((linked_iff_torus_conjugate h i j).2 e)⟩
  · exact Or.inr ⟨(torus_conjugate_corner_entry_eq h _).symm.trans (a _ hs), s2 fun i j hij e => b i j hij ((linked_iff_torus_conjugate h i j).2 e)⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.m3 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], Loc.LocalPublishedTheorems → SoV Ω l → D.Fin0 → M3 M.gr (PadicAlgCl l) M.x0 M.eqns.ideal := by
  intro Ω _ _ _ l _ c D hD M _ hL hS hF x₁ h1 hn hp _
  obtain ⟨ξ₁, rfl⟩ := ptLift D hD M x₁ h1
  obtain ⟨t, r, hr, h⟩ := ptScale D hD M hF ξ₁
  obtain ⟨-, -, s3, -, s5⟩ := signs D hD M hF ξ₁
  have n02 : ¬ Ge r 0 2 := fun e => s3 hp ((linked_iff_torus_conjugate h 0 2).1 e)
  have hd : DiagType (M.rep ξ₁) := by
    rcases tri D hD hL r hr with a | a | a
    · obtain ⟨p1, -, -, -, -, p6, -⟩ := ptIn D hD _ r hr
      exact absurd ((geAlg _ r _ p1 p6).2.2.2.2.1.1 a 0 2) n02
    · exact fun i j hij u v => a i j hij ((linked_iff_torus_conjugate h i j).2 u) ((linked_iff_torus_conjugate h j i).2 v)
    · exact absurd a.1 n02
  have hne : ((D.th D.s0 : c.O) : PadicAlgCl l) ≠ ((D.al D.s0 : c.O) : PadicAlgCl l) := fun e => by
    have hinj := (facts D hD).2.2.2.2.2.2.1
    have : (0 : Fin 4) = 2 := hinj (Subtype.ext e)
    exact absurd this (by decide)
  have key : ∀ x : M.A →ₐ[c.O] PadicAlgCl l, OnS M.eqns.ideal x → Same0 M.gr x (ξ₁.comp M.toSS) →
      (M.rep ξ₁ D.s0 0 0 = ((D.th D.s0 : c.O) : PadicAlgCl l) ∧ NegZero M.gr x) ∨
      (M.rep ξ₁ D.s0 0 0 = ((D.al D.s0 : c.O) : PadicAlgCl l) ∧ PosZero M.gr x) := by
    intro x hx h0
    obtain ⟨ξ, rfl⟩ := ptLift D hD M x hx
    obtain ⟨q1, q2⟩ := s5 ξ fun b hb => (h0 b hb).symm
    rw [q1]
    exact diagonal_type_corner_cases D hD M hS hF ξ (q2 hd)
  rcases diagonal_type_corner_cases D hD M hS hF ξ₁ hd with ⟨a, -⟩ | ⟨a, -⟩
  · refine Or.inr ?_
    rintro ⟨x, hx, -, hnn, h0⟩
    rcases key x hx h0 with ⟨-, b⟩ | ⟨b, -⟩
    · exact hnn b
    · exact hne (a.symm.trans b)
  · refine Or.inl ?_
    rintro ⟨x, hx, -, hnn, h0⟩
    rcases key x hx h0 with ⟨b, -⟩ | ⟨-, b⟩
    · exact hne (b.symm.trans a)
    · exact hnn b
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoIrr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem twoIrr_entry {K : Type} [Field K] (t : Kˣ × Kˣ) (X : M4 K) (i j : Fin 4) :
    tconj t X i j = 0 ↔ X i j = 0 := by
  show (wv t (wt i j) : K) * X i j = 0 ↔ _
  rw [mul_eq_zero, or_iff_right (Units.ne_zero _)]

private theorem twoIrr_ge {H K : Type} [Group H] [Field K] (t : Kˣ × Kˣ) (r r' : H →* M4 K)
    (h : ∀ g, r g = tconj t (r' g)) (i j : Fin 4) : Ge r i j ↔ Ge r' i j := by
  unfold Ge
  refine exists_congr fun g => ?_
  rw [h g, Ne, Ne, twoIrr_entry]

private theorem twoIrr_irr {H K : Type} [Group H] [Field K] (t : Kˣ × Kˣ) (r r' : H →* M4 K)
    (h : ∀ g, r g = tconj t (r' g)) (hr : Irr r) : Irr r' := by
  let L : M4 K →ₗ[K] M4 K :=
    { toFun := fun X => Matrix.of fun i j => (((wv t (wt i j))⁻¹ : Kˣ) : K) * X i j
      map_add' := fun X Y => by ext i j; simp [mul_add]
      map_smul' := fun a X => by ext i j; simp [mul_left_comm] }
  have hL : ∀ X, L (tconj t X) = X := fun X => by
    ext i j
    show (((wv t (wt i j))⁻¹ : Kˣ) : K) * ((wv t (wt i j) : K) * X i j) = X i j
    rw [Units.inv_mul_cancel_left]
  unfold Irr at *
  rw [eq_top_iff]
  intro X _
  have h1 : tconj t X ∈ Submodule.span K (Set.range r) := by rw [hr]; trivial
  have h2 := Submodule.mem_map_of_mem (f := L) h1
  rw [hL, Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact ⟨g, by rw [h g, hL]⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.twoIrr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], Loc.LocalPublishedTheorems → SoV Ω l → D.Fin0 → D.NoEnd → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, TwoSigned M.gr (ξ.comp M.toSS) → Irr (M.rep ξ) := by
  intro Ω _ _ _ l _ c D hD M _ hP hSo hF hNE ξ h2
  obtain ⟨t, r, hr, hrt⟩ := ptScale D hD M hF ξ
  have hge := twoIrr_ge t r _ hrt
  obtain ⟨hn, hp, -⟩ := signs D hD M hF ξ
  rcases tri D hD hP r hr with h | h | ⟨h02, h20, h⟩
  · exact twoIrr_irr t r _ hrt h
  · exfalso
    rcases diagCases D hD hSo r hr h with ⟨-, h⟩ | ⟨-, h⟩
    · exact h2.1 (hn fun i j hij hg => h i j hij ((hge i j).2 hg))
    · exact h2.2 (hp fun i j hij hg => h i j hij ((hge i j).2 hg))
  · exfalso
    obtain ⟨ξ₀, h₀⟩ := ptLimit D hD M hF ξ (h.imp (fun h i j hij hg => h i j hij ((hge i j).2 hg))
      (fun h i j hij hg => h i j hij ((hge i j).2 hg)))
    obtain ⟨t₀, r₀, hr₀, hrt₀⟩ := ptScale D hD M hF ξ₀
    have hge₀ := twoIrr_ge t₀ r₀ _ hrt₀
    obtain ⟨hm, -, -, -, -, he, -⟩ := ptIn D hD (PadicAlgCl l) r₀ hr₀
    obtain ⟨-, -, -, -, -, h6⟩ := geAlg (PadicAlgCl l) r₀ _ hm he
    have hb : ∀ g, IsBlock (r₀ g) := fun g i j hij => by
      rw [hrt₀, twoIrr_entry, h₀, if_neg hij]
    have key : ∀ i j, lamW i = lamW j → Ge r i j → Ge r₀ i j := fun i j hij hg => by
      obtain ⟨g, hg⟩ := (hge i j).1 hg
      exact (hge₀ i j).2 ⟨g, by rw [h₀, if_pos hij]; exact hg⟩
    exact hNE r₀ hr₀ hb (h6 (key 0 2 (by decide) h02) (key 2 0 (by decide) h20) hb)
end

