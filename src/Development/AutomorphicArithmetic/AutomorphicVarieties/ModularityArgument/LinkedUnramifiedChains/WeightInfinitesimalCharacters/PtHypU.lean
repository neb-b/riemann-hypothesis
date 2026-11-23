module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.TypeIIOfBlochKatoLocalPoint

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

theorem UpperTheory.V.Z.J.ptHyp_ofU :
    U3.CohInp → Z.Kato.KatoTwo → Th.RigI → Th.RigII → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ), Aut.AutB D ι g₁ → Aut.LemW D ι g₁ →
      ∀ x₀ : S.R →ₐ[c.O] c.O, IsBase D.η D.Ψ S.r.hom x₀ → PtHyp D.η S.r.hom x₀ := by
  intro hC hK hRI hRII Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM S _ ι hB hW x₀ hx
  have hCob {Γ κ : Type} [Group Γ] [CommRing κ] (r : Γ →* GG (m := 3) (R := κ))
      (γ : Γ → Matrix (Fin 3) (Fin 3) κ) (h : γ ∈ ReciprocityTheory.Gal.B1 (adRep r)) :
      ∃ X, γ = cob r X := by
    obtain ⟨X, hX⟩ := LinearMap.mem_range.mp h
    refine ⟨-X, funext fun g => ?_⟩
    rw [← hX]
    show adRep r g X - X = -X - adRep r g (-X)
    rw [map_neg]
    abel
  have h0 : push (toBar x₀) S.r.hom = r0 D.η D.ΨQ := by
    let φ := algebraMap c.O (PadicAlgCl l)
    change (GG.map φ).comp (push x₀ S.r.hom) = _
    rw [show push x₀ S.r.hom = r0 D.η D.Ψ from hx]
    refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
    show (tor c.O (D.Ψ g) : Matrix (Fin 3) (Fin 3) c.O).map φ =
      tor (PadicAlgCl l) (Units.map φ.toMonoidHom (D.Ψ g))
    rw [tor_val, tor_val, Matrix.diagonal_map (map_zero φ)]
    congr 1
    funext i
    exact congrArg Units.val (map_zpow (Units.map φ.toMonoidHom) (D.Ψ g) (wt1 i))
  refine ⟨fun f hf hU hL => ?_, fun j hj F hF hw => ?_, fun f hf F hF => ?_⟩
  · rw [h0]
    exact pt_fixed hC D hM (isPt_push D hM S f hf) hU hL
  · have hLoc : IsLocPt (toBar x₀) := by
      intro y hy
      have hsurj : Function.Surjective x₀ := fun a => ⟨algebraMap c.O S.R a, x₀.commutes a⟩
      have hmax : (Ideal.comap (x₀ : S.R →+* c.O) (maximalIdeal c.O)).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ hsurj
      have hy' : y ∈ Ideal.comap (x₀ : S.R →+* c.O) (maximalIdeal c.O) :=
        IsLocalRing.eq_maximalIdeal hmax ▸ hy
      have hb : ¬ IsUnit (x₀ y) := (IsLocalRing.mem_maximalIdeal _).mp hy'
      change ‖(x₀ y : PadicAlgCl l)‖ < 1
      by_cases hz : x₀ y = 0
      · simp [hz]
      have hn : (IsDiscreteValuationRing.addVal c.O (x₀ y)).toNat ≠ 0 := by
        rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff,
          IsDiscreteValuationRing.addVal_eq_top_iff]
        exact fun h => h.elim hb hz
      have hl : ((l : ℝ)⁻¹) < 1 :=
        inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
      have hlt := pow_lt_one₀ (by positivity) hl hn
      rw [← normO l c.O (x₀ y) hz] at hlt
      exact lt_of_not_ge fun hge => (not_lt_of_ge (one_le_pow₀ hge)) hlt
    have h1 := tanCoc_isBK hC D hM S F (hF ▸ hLoc)
    rw [hF, h0] at h1
    rw [h0]
    exact hCob _ _ (bloch_kato_nonpositive_weight hC D j hj _ h1.1 hw h1.2)
  · have h1 := tanCoc_isBK hC D hM S F (hF ▸ hf.1)
    rw [hF] at h1
    have hp := isPt_push D hM S f hf.1
    have hPush {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R]
        [CommRing κ] [Algebra O κ] (f' : R →ₐ[O] κ) (r : Γ →* GG (m := 3) (R := R)) :
        IsPush (f'.comp (entAlg O r).val) r (push f' r) := by
      intro g
      refine ⟨rfl, fun a b => ⟨?_, rfl⟩⟩
      unfold entAlg
      exact Algebra.subset_adjoin ⟨g, a, b, rfl⟩
    have hz : Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom)) := by
      rcases (twoPt_shape S D.gd.l_odd hM f hf).1 with h | h
      · exact hRI D hM S f hf.1 hp.mult ι h (hB U S _ _ hp.mult (hPush f _) h)
      · exact Z.J.typeII_of_blochKato_localPoint hC hK hRII D hM S f hf.1 ι h
          (hW U S _ _ (hPush f _) h (typeII_facts hC D hM hp h).1)
    exact hCob _ _ (hz _ h1.1 h1.2)
