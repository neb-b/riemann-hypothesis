module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.CubeMapTripleProductUnique
section
noncomputable section

namespace GlobalTheory.SemiAbelianTripleChecks

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}

theorem psum_singleton (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (x : Fin 3 → (T ⟶ G)) (i : Fin 3) :
    psum G x {i} = x i := by
  have h : (List.finRange 3).filter (· ∈ ({i} : Finset (Fin 3))) = [i] := by
    fin_cases i <;> decide
  unfold psum
  rw [h]
  have : padd G (x i) (pzero G T) = x i * 1 := rfl
  simp only [List.foldr_cons, List.foldr_nil]
  rw [this, _root_.mul_one]

theorem cubeMap_tripleProduct_unique {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (m m' : CubeMap G' G) (h : m.F = m'.F) : m.F3 = m'.F3 := by
  have key : ∀ i : Fin 3, m.F3 ≫ (x3 G i).left = m'.F3 ≫ (x3 G i).left := fun i => by
    have h1 := m.psum_comm {i}
    have h2 := m'.psum_comm {i}
    rw [psum_singleton, psum_singleton] at h1 h2
    rw [← h1, ← h2, h]
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  apply pullback.hom_ext
  · exact k0
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]; exact k1
    · rw [Category.assoc, Category.assoc]; exact k2

theorem sabMap_ext {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m m' : SABMap t' t f) (h : m.φ = m'.φ) :
    m = m' := by
  obtain ⟨⟨F, F3, e, he, hp⟩, c, b, a, l⟩ := m
  obtain ⟨⟨F', F3', e', he', hp'⟩, c', b', a', l'⟩ := m'
  have h3 : F3 = F3' := cubeMap_tripleProduct_unique ⟨F, F3, e, he, hp⟩ ⟨F', F3', e', he', hp'⟩ h
  have h1 : F = F' := h
  have h2 : e = e' := b.trans b'.symm
  subst h1 h2 h3
  rfl

end GlobalTheory.SemiAbelianTripleChecks
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.W0EqOfRtEq
section
noncomputable section

namespace GlobalTheory.HostProbe

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem goodAt_iff (l : Level H) {p : ℕ} (hp : p.Prime) : l.GoodAt p ↔ ∀ k, l.M ≠ p ^ k := by
  have h3 := l.three_le
  have hM : l.M ≠ 0 := by omega
  have hmul : p ^ l.M.factorization p * (l.M / p ^ l.M.factorization p) = l.M :=
    Nat.ordProj_mul_ordCompl_eq_self _ _
  unfold Level.GoodAt
  constructor
  · intro h k hk
    rw [hk] at h
    simp [hp.factorization_pow, Nat.div_self (pow_pos hp.pos k)] at h
  · intro h
    set c := l.M / p ^ l.M.factorization p with hc
    have hodd : Odd c := by
      have := l.odd
      rw [← hmul] at this
      exact (Nat.odd_mul.1 this).2
    have h1 : c ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hmul
      exact h _ hmul.symm
    obtain ⟨t, ht⟩ := hodd
    omega

end GlobalTheory.HostProbe
end
end

