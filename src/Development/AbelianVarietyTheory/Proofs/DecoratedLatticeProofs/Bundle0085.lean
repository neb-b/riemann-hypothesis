module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateUnitaryKTypeSameWeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMo
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0117
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimUnitaryKTypeEqDualWeylModule
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms
open scoped InnerProductSpace Matrix

noncomputable section

namespace GlobalTheory.DualWeylType

open GlobalTheory.ConjugateType

theorem dual_weyl_type : ∀ (k n : ℕ) (h : k = n) (lam : DomWeight n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (lamH : Fin k → ℝ), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ (Formalism.QuantumDeterminants.lowK (allPos k) lamH) ⊤ → (∀ i : Fin k, -lamH (Fin.rev i) = (lam.w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∃ (j : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ℕ) (b : Module.Basis (Fin d) ℂ H), (∀ ξ, j ξ ∈ delSq ℂ n lam) ∧ (∀ p ∈ delSq ℂ n lam, ∃ ξ, j ξ = p) ∧ (∀ a a', normFock lam (j (b a)) (j (b a')) = if a = a' then 1 else 0) ∧ ∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ ξ, j (σ (g.submatrix (Fin.cast h) (Fin.cast h)) ξ) = (g.det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ gᴴ (j ξ) := by
  intro k n h lam H _ _ _ σ lamH hσ hK hrho

  obtain ⟨hσ', hK'⟩ := GlobalTheory.ConjTwist.conj_twist_isKTypeOf k _ 0 H σ hσ hK

  obtain ⟨E, iE1, iE2, iE3, π, J, hJ, hπ, hπK, hπJ⟩ := exists_conjugate_type k _ H _ hσ' hK'
  have hJσ : ∀ g u, π g (J u) = J (σ g u) := by
    intro g u
    rw [hπJ]
    simp only [zpow_zero, one_smul, map_star_star]

  have hlow : Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -lamH (Fin.rev i)) =
      fun a => ((0 : ℤ) : ℝ) - Formalism.QuantumDeterminants.lowK (allPos k) lamH (Fin.rev a) := by
    rw [GlobalTheory.ConjTypeW.lowK_neg_rev]
    funext a
    simp
  have hnt : Nontrivial E := by
    obtain ⟨-, -, -, ⟨v, -, hv0, -⟩, -⟩ := hπK
    exact ⟨⟨v, 0, hv0⟩⟩
  have hHC : IsHCTypeU k (fun i => -lamH (Fin.rev i)) π := ⟨hnt, iE3, hπ, by rw [hlow]; exact hπK⟩

  obtain ⟨jE, hmem, hsurj, hfock, heq⟩ :=
    GlobalTheory.WeylConjType.exists_conj_weyl k n h lam _ hrho E π hHC

  let j : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    { toFun := fun ξ => jE (J ξ)
      map_add' := fun x y => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c x => by
        rw [map_smulₛₗ, map_smulₛₗ, RingHom.id_apply, Complex.conj_conj] }
  have hj : ∀ ξ, j ξ = jE (J ξ) := fun _ => rfl

  let Φ : H →ₗ[ℂ] ConjSp E :=
    { toFun := fun ξ => ConjSp.mk (J ξ)
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by
        show ConjSp.mk (J (c • x)) = c • ConjSp.mk (J x)
        have e := (ConjSp.mkL E).map_smulₛₗ (starRingEnd ℂ c) (J x)
        rw [Complex.conj_conj] at e
        rw [map_smulₛₗ]
        exact e }
  have hΦ : Function.Bijective Φ := hJ
  let Ψ : H ≃ₗ[ℂ] ConjSp E := LinearEquiv.ofBijective Φ hΦ
  let f := stdOrthonormalBasis ℂ (ConjSp E)
  refine ⟨j, _, f.toBasis.map Ψ.symm, fun ξ => hmem _, fun p hp => ?_, fun a a' => ?_, fun g hg ξ => ?_⟩
  · obtain ⟨η, rfl⟩ := hsurj p hp
    obtain ⟨ξ, rfl⟩ := hJ.2 η
    exact ⟨ξ, rfl⟩
  · have hb : ∀ a, J ((f.toBasis.map Ψ.symm) a) = ConjSp.out (f a) := by
      intro a
      rw [Module.Basis.map_apply, OrthonormalBasis.coe_toBasis]
      have := Ψ.apply_symm_apply (f a)
      exact this
    rw [hj, hj, hfock, hb, hb]
    show ⟪f a', f a⟫_ℂ = _
    rw [orthonormal_iff_ite.1 f.orthonormal]
    rcases eq_or_ne a a' with rfl | hA
    · simp
    · rw [if_neg hA.symm, if_neg hA]
  · rw [hj, hj, ← hJσ, heq g hg]

end GlobalTheory.DualWeylType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalSpanSeparately
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory

theorem exists_finset_eval_injective {Z : Type} (T : Submodule ℂ (Z → ℂ))
    [FiniteDimensional ℂ T] :
    ∃ Y : Finset Z, ∀ g ∈ T, (∀ y ∈ Y, g y = 0) → g = 0 := by
  classical
  let φ : Z → Module.Dual ℂ T := fun z => (LinearMap.proj z).comp T.subtype
  have hfg : (Submodule.span ℂ (Set.range φ)).FG := IsNoetherian.noetherian _
  obtain ⟨s', hs', hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  rw [← Set.image_univ] at hs'
  obtain ⟨Y, -, rfl⟩ := Finset.subset_set_image_iff.1 hs'
  refine ⟨Y, fun g hg hY => ?_⟩
  have hle : Submodule.span ℂ (Set.range φ) ≤ LinearMap.ker (Module.Dual.eval ℂ T ⟨g, hg⟩) := by
    rw [hspan, Submodule.span_le]
    intro ψ hψ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hψ
    obtain ⟨y, hy, rfl⟩ := hψ
    simp [φ, hY y hy]
  funext z
  have hz := hle (Submodule.subset_span ⟨z, rfl⟩)
  simpa [φ] using hz

theorem finiteDimensional_span_separately (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type)
    (S : ∀ i, Submodule ℂ (X i → ℂ)) (hS : ∀ i, FiniteDimensional ℂ (S i)) :
    FiniteDimensional ℂ (Submodule.span ℂ
      {f : (∀ i, X i) → ℂ | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i}) := by
  classical
  choose Y hY using fun i => @exists_finset_eval_injective (X i) (S i) (hS i)
  let P : Submodule ℂ ((∀ i, X i) → ℂ) :=
    { carrier := {f | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i}
      add_mem' := fun {f g} hf hg i x => (S i).add_mem (hf i x) (hg i x)
      zero_mem' := fun i x => (S i).zero_mem
      smul_mem' := fun c f hf i x => (S i).smul_mem c (hf i x) }
  have hle : Submodule.span ℂ
      {f : (∀ i, X i) → ℂ | ∀ i x, (fun y => f (Function.update x i y)) ∈ S i} ≤ P :=
    Submodule.span_le.2 fun f hf => hf
  let L : P →ₗ[ℂ] ((∀ i, Y i) → ℂ) :=
    { toFun := fun f y => (f : (∀ i, X i) → ℂ) (fun i => (y i : X i))
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hfP : ∀ i x, (fun y => (f : (∀ i, X i) → ℂ) (Function.update x i y)) ∈ S i := f.2
    have key : ∀ A : Finset ι, ∀ x : ∀ i, X i, (∀ j ∉ A, x j ∈ Y j) →
        (f : (∀ i, X i) → ℂ) x = 0 := by
      intro A
      induction A using Finset.induction_on with
      | empty =>
        intro x hx
        have h0 := congrFun hf (fun j => ⟨x j, hx j (by simp)⟩)
        simpa [L] using h0
      | @insert i A hiA ih =>
        intro x hx
        have hg : (fun y => (f : (∀ i, X i) → ℂ) (Function.update x i y)) = 0 := by
          refine hY i _ (hfP i x) ?_
          intro y hy
          apply ih
          intro j hj
          by_cases hji : j = i
          · subst hji
            simpa using hy
          · rw [Function.update_of_ne hji]
            exact hx j (by simp [hji, hj])
        have h1 := congrFun hg (x i)
        simpa using h1
    apply Subtype.ext
    funext x
    exact key Finset.univ x (fun j hj => absurd (Finset.mem_univ j) hj)
  have : FiniteDimensional ℂ P := Module.Finite.of_injective L hL
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqMulOfSplit
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem charAt_eq_locChar_mul_locChar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) * (locChar χ w' (Units.map (toCompl h').toMonoidHom x) : ℂˣ) := by
  intro F E _ _ _ _ _ χ v w h w' h' hne hall x
  have key : ideleAt F E v x = locIdele F w (Units.map (toCompl h).toMonoidHom x) *
      locIdele F w' (Units.map (toCompl h').toMonoidHom x) := by
    refine Units.ext (tens_ext ?_ ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun u => ?_)))
    · rw [Units.val_mul, map_mul, infTens_locIdele, infTens_locIdele, mul_one]
      exact map_extUnit_zero (fstA F) _ _ (fun a => rfl) x
    · rw [Units.val_mul, map_mul (finTens F E), map_mul, finTens_locIdele, finTens_locIdele]
      have hc : ∀ u' : HeightOneSpectrum (𝓞 F), Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u') (AlgHom.id F E)
          (finTens F E (ideleAt F E v x)) = (unitFin F E u' (ideleAt F E v x) : Fv F u' ⊗[F] E) := fun u' => by
        change ((Algebra.TensorProduct.map _ _).comp (Algebra.TensorProduct.map _ _)) _ = _
        rw [← Algebra.TensorProduct.map_comp]
        rfl
      change _ = Neutral.B1.finiteSingle E w (Units.map (toCompl h).toMonoidHom x) u *
        Neutral.B1.finiteSingle E w' (Units.map (toCompl h').toMonoidHom x) u
      by_cases hu : u.under (𝓞 F) = v
      · rw [finAdEquiv_apply hu, hc, unitFin_ideleAt_self]
        rcases (hall u).1 hu with rfl | rfl
        · rw [finSingle_self, finSingle_ne hne, mul_one]
          rfl
        · rw [finSingle_self, finSingle_ne (Ne.symm hne), one_mul]
          rfl
      · rw [finAdEquiv_apply rfl, hc, unitFin_ideleAt_ne hu, Units.val_one, map_one,
          finSingle_ne (fun e => hu (by rw [e]; exact h)), finSingle_ne (fun e => hu (by rw [e]; exact h')), mul_one]
  show ((χ (ideleAt F E v x) : Circle) : ℂ) = _
  rw [key, map_mul]
  rfl

end GlobalTheory.LFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInert
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.LFun

theorem ideleAt_eq_locIdele_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w)
    (x : (Fv F v ⊗[F] E)ˣ) :
    ideleAt F E v x = locIdele F w (Units.map (toCompl h).toMonoidHom x) := by
  refine eq_locIdele ?_ ?_
  · exact map_extUnit_zero (fstA F) (inFin v) (inFin_mul v) (fun _ => rfl) x
  · refine FiniteAdeleRing.ext _ fun u => ?_
    rw [finAdEquiv_apply rfl]
    have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F (u.under (𝓞 F))) (AlgHom.id F E)
        (finTens F E (ideleAt F E v x : AF F ⊗[F] E)) = (unitFin F E (u.under (𝓞 F)) (ideleAt F E v x) : Fv _ _ ⊗[F] E) := by
      change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) _) = _
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
      rfl
    rw [e]
    by_cases hu : u.under (𝓞 F) = v
    · obtain rfl : u = w := (InertChart.under_eq_iff hw u).1 hu
      subst h
      rw [unitFin_ideleAt_self]
      exact (finSingle_self u _).symm
    · rw [unitFin_ideleAt_ne hu, Units.val_one, map_one]
      exact (finSingle_ne (fun e : u = w => hu (e ▸ h)) _).symm

theorem charAt_eq_locChar_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) := by
  intro F E _ _ _ _ _ χ v w h hw x
  show ((χ (ideleAt F E v x) : Circle) : ℂ) = ((Circle.toUnits (χ (locIdele F w _)) : ℂˣ) : ℂ)
  rw [GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw x]
  rfl

end GlobalTheory.LFun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantSphericalCoefficientEqZeroOrZonal
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.ZonalCoeff

open Formalism.UG

theorem apply_heckeVec {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}
    (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Formalism.UG.Hecke ℂ K) (ρ : Representation ℂ G V) (x : V)
    (l : V →ₗ[ℂ] ℂ) : l (GlobalTheory.LFun.heckeVec ρ K h x) = ∑ᶠ c : G ⧸ K, h c.out * l (ρ c.out x) :=
  (l.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK hh ρ x)).trans (finsum_congr fun c => by simp)

theorem eq_zero_of_doset_sum {G : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K) {w : G → ℂ}
    (hw : IsBiInv K w) (g : G) (e : ∑ᶠ c : G ⧸ K, dosetInd ℂ K g c.out * w c.out = 0) : w g = 0 := by
  classical
  have hfin := Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem G K ℂ g).2
  have hmem : ∀ c ∈ hfin.toFinset, c.out ∈ DoubleCoset.doubleCoset g (K : Set G) K := fun c hc => by
    by_contra hn
    exact (hfin.mem_toFinset.1 hc) (Set.indicator_of_notMem hn _)
  have h1 : ∀ c ∈ hfin.toFinset, dosetInd ℂ K g c.out * w c.out = w g := fun c hc => by
    obtain ⟨a, ha, b, hb, e'⟩ := DoubleCoset.mem_doubleCoset.1 (hmem c hc)
    rw [dosetInd, Set.indicator_of_mem (hmem c hc), Pi.one_apply, one_mul, e']
    exact hw ⟨a, ha⟩ ⟨b, hb⟩ g
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ fun c hc =>
      hfin.mem_toFinset.2 (left_ne_zero_of_mul hc),
    Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul] at e
  refine (mul_eq_zero.1 e).resolve_left (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), ?_⟩))
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  refine hfin.mem_toFinset.2 ?_
  change dosetInd ℂ K g _ ≠ 0
  rw [dosetInd, Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, k, k.2, by rw [hk, one_mul]⟩)]
  exact one_ne_zero

theorem coeff_zero_or_zonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x = 0 → ∀ g, ℓ (ρ g x) = 0) ∧ (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α fun g => ℓ (ρ g x) / ℓ x) := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ x α hx l hl
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n
  have hbi : IsBiInv (KU σ n) fun g => l (ρ g x) := fun a b g => by
    beta_reduce
    rw [map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ b.2, hl _ a.2]
  refine ⟨fun h0 g => eq_zero_of_doset_sum hK hbi g ?_, fun h0 => ⟨fun a b g => ?_, ?_, fun h hh => ?_⟩⟩
  · have hm := Formalism.UG.Final.DosetIndMem _ (KU σ n) ℂ g
    rw [← apply_heckeVec hK hm, hx.2.2 _ hm, map_smul, h0, smul_zero]
  · exact congrArg (· / l x) (hbi a b g)
  · simpa using div_self h0
  · have e := apply_heckeVec hK hh ρ x ((l x)⁻¹ • l)
    rw [hx.2.2 h hh, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ h0, mul_one] at e
    rw [e]
    exact finsum_congr fun c => by simp [div_eq_inv_mul]

end GlobalTheory.ZonalCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLatticeFrameAtPlaceDirectSumBlockDiagonal
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem latAt_sumLat_self {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) :
    latAt w (sumLat finSumFinEquiv L L) = sumLat finSumFinEquiv (latAt w L) (latAt w L) := by
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  have hl0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e (x + y) 0 = pairVec e x 0 + pairVec e y 0 := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hr0 : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e 0 (x + y) = pairVec e 0 x + pairVec e 0 y := by
    intro X _ x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hls : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e (c • x) 0 = c • pairVec e x 0 := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hrs : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E), pairVec e 0 (c • x) = c • pairVec e 0 x := by
    intro c x; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hz : pairVec e (0 : Fin n → w.adicCompletion E) 0 = 0 := by
    funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hsplit : ∀ (x y : Fin n → w.adicCompletion E), pairVec e x y = pairVec e x 0 + pairVec e 0 y := by
    intro x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  set φ : (Fin n → E) → (Fin n → w.adicCompletion E) := fun x i => algebraMap E (w.adicCompletion E) (x i)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_sumLat] at hx ⊢
    exact ⟨Submodule.subset_span ⟨_, hx.1, rfl⟩, Submodule.subset_span ⟨_, hx.2, rfl⟩⟩
  · intro z hz'
    rw [← pairVec_eta e z, pairVec_mem_sumLat] at hz'
    rw [← pairVec_eta e z, hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inl i)) := ⟨_, rfl⟩
      have hu' := hz'.1
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e y 0, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨hy, L.zero_mem⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hl0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hls]; exact Submodule.smul_mem _ c hx
    · obtain ⟨u, hu⟩ : ∃ u, u = fun i => z (e (.inr i)) := ⟨_, rfl⟩
      have hu' := hz'.2
      rw [← hu] at hu' ⊢
      clear hu
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e 0 y, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨L.zero_mem, hy⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => rw [hz]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [hr0]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [hrs]; exact Submodule.smul_mem _ c hx

theorem isFrameAt_sumLat_blkGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (w.adicCompletion E)), IsFrameAt w L a → IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := by
  intro E _ _ w n L a ha y
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  rw [latAt_sumLat_self, ← pairVec_eta e y, val_blkGL, blkMat_mulVec, pairVec_mem_sumLat,
    ← ha, ← ha]
  constructor
  · intro h; exact ⟨fun i => by simpa using h (e (.inl i)), fun i => by simpa using h (e (.inr i))⟩
  · rintro ⟨h1, h2⟩ j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [h1, h2]

end GlobalTheory.LFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LvTwDivDvInertEqStdL
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem LvTw_div_dv_inert_eq_stdL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (α : Fin (r / 2) → ℂˣ) (s : ℂ), Module.finrank F E = 2 → IsInertAt F E v w → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → B w = bcParam r α → LvTw B m v (s + 1 / 2) / dv E r b v s = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL (qV F v) r α (((m w)⁻¹ : ℂˣ) : ℂ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac (qV F v) r b s := by
  intro F E _ _ _ _ _ B m v w r b α s h2 hw hU hB
  have hv := InertChart.under_eq_iff hw
  have hq := InertChart.absNorm_eq h2 hw
  have hq0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (one_lt_absNorm v).ne_bot
  have hns := not_isSplit_of_isInertAt hw
  rw [LvTw_inert B m hv hq, hB]
  congr 1
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL, Units.val_inv_eq_inv_val]
    congr 2
    rw [npow, show qV F v = Ideal.absNorm v.asIdeal from rfl, pow_two,
      show -(2 * (s + 1 / 2)) = -(s + 1 / 2) + -(s + 1 / 2) by ring, Complex.cpow_add _ _ hq0,
      Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  · rw [dv, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [locL, etaFam_of_unram hU, eulerFac_singleton, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.etaL, Units.val_pow_eq_pow_val, npow,
      show qV F v = Ideal.absNorm v.asIdeal from rfl]
    have he : ((etaU E v : ℂˣ) : ℂ) = -1 := by simp [etaU, hns]
    rw [he]

end GlobalTheory.LFun
end

