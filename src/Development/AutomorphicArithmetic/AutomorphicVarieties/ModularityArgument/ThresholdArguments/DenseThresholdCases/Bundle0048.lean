module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.RelOfAct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.ResEq2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ChainBetweenPairs

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OffDiagonalNilpotentRankFour
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
theorem UpperTheory.V.Ws.off_diagonal_nilpotent_rank_four :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PotentialModularityTower ι X J → ∀ (v : T.ι) (i j : Fin 4), i ≠ j → ∀ (q : Ideal X.B), q.IsPrime → J ≤ q → (maximalIdeal c'.O).map (algebraMap c'.O X.B) ≤ q →
      (∀ s ∈ T.U1 v, X.ψ v i s - X.ψ v j s ∈ q) → ∀ dv : ℕ, dv * Nat.card T.ι = T.d → ringKrullDim (X.B ⧸ q) + dv ≤ (2 * T.d + 1 : ℕ) := by
  classical
  intro _ Ω _ _ _ l _ c D T hFit _ ι c' h X J hPM v i j hij q hq hJ hϖ hU dv hdv
  have hOk := hFit.1
  have hl2 : l ≠ 2 := by
    rcases hFit.2 with h | h
    · exact h.1.1.l_odd
    · exact h.1.1.l_odd
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsGalois T.F Ω := IsAlgClosure.isGalois T.F Ω
  haveI : Nonempty T.ι := ⟨v⟩
  have hg : 0 < Nat.card T.ι := Nat.card_pos
  haveI hcD : ∀ u, CompactSpace (Dec (F := T.F) (T.pl u)) := fun u =>
    isCompact_iff_compactSpace.1 (isClosed_Dec (T.pl u)).isCompact
  let I : ∀ u, Subgroup (Dec (F := T.F) (T.pl u)) := fun u => (Ine (F := T.F) (T.pl u)).subgroupOf _
  have hs : ∀ u, ∃ s : Fin dv → Dec (F := T.F) (T.pl u), (∀ k, s k ∈ I u) ∧ Pins l (I u) (Set.range s) := fun u => by
    obtain ⟨w, hw, hlw, hd⟩ := UpperTheory.exists_place_over_l_locDeg_mul_card_eq D T u
    obtain ⟨A⟩ := UpperTheory.nonempty_localWeilData_decompositionGroup_of_mem_place l (T.pl u) w hw hlw
    obtain rfl : locDeg w = dv := Nat.eq_of_mul_eq_mul_right hg (hd.trans hdv.symm)
    exact UpperTheory.exists_pinning_elements_of_locAb l _ _ _ A
  choose s hsI hsP using hs
  obtain ⟨s0, hs0, hP0⟩ := UpperTheory.exists_mem_pins_insert_ker_of_padic_character l hl2 _ (I v) ((isClosed_Ine (T.pl v)).preimage continuous_subtype_val)
    ((cycZ T.F Ω l).comp (Dec (F := T.F) (T.pl v)).subtype) ((continuous_cycZ T.F Ω l).comp continuous_subtype_val)
  obtain ⟨a, ha, ha'⟩ : ∃ a : Fin 4, (a = j ∨ j = i.rev) ∧ ∀ m : Fin 4, m = a ∨ m = a.rev ∨ m = i ∨ m = i.rev :=
    (by decide : ∀ i j : Fin 4, i ≠ j → ∃ a : Fin 4, (a = j ∨ j = i.rev) ∧
      ∀ m : Fin 4, m = a ∨ m = a.rev ∨ m = i ∨ m = i.rev) i j hij
  let x : (T.ι × Fin dv) ⊕ ({u // u ≠ v} × Fin dv) ⊕ Unit → X.B :=
    Sum.elim (fun y => X.ψ y.1 a (s y.1 y.2) - 1)
      (Sum.elim (fun y => X.ψ y.1.1 i (s y.1.1 y.2) - 1) fun _ => X.ψ v i s0 - X.ψ v j s0)
  have hm : ∀ u m (t : Dec (F := T.F) (T.pl u)), t ∈ I u → X.ψ u m t - 1 ∈ maximalIdeal X.B := fun u m t ht => by
    obtain ⟨-, κ, hκ⟩ := UpperTheory.deformationSpace_local_characters_continuous D T hOk c' h X _ (residue X.B) (fun b hb => by
      rw [(residue_eq_zero_iff b).2 hb]; exact zero_mem _) (fun b hb => (residue_eq_zero_iff _).2 (map_nonunit _ b hb))
    have h1 := ((hκ u m).2.2 t ht).1
    rw [(hκ u m).1, maximalIdeal_eq_bot, Ideal.mem_bot, ← map_one (residue X.B), ← map_sub, residue_eq_zero_iff] at h1
    exact h1
  have hdim := UpperTheory.krullDim_quotient_le_card_of_radical_parameters X.B q _ x ?_ ?_
  · have hc : Nat.card ((T.ι × Fin dv) ⊕ ({u // u ≠ v} × Fin dv) ⊕ Unit) + dv = 2 * T.d + 1 := by
      have h1 : Nat.card {u // u ≠ v} + 1 = Nat.card T.ι := by
        rw [← Finite.card_option]
        exact Nat.card_congr (Equiv.optionSubtypeNe v)
      simp only [Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin dv), Fintype.card_fin, Nat.card_unique]
      rw [← hdv, ← h1]
      ring
    rw [← hc, Nat.cast_add]
    gcongr
  · rintro (y | y | y)
    · exact hm _ _ _ (hsI _ _)
    · exact hm _ _ _ (hsI _ _)
    · simpa [x] using sub_mem (hm v i s0 hs0) (hm v j s0 hs0)
  intro p hp hqp hx
  haveI : IsLocalRing (X.B ⧸ p) := IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk p) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨h0, κ, hκ⟩ := UpperTheory.deformationSpace_local_characters_continuous D T hOk c' h X _ (Ideal.Quotient.mk p) (fun b hb => map_nonunit _ b hb)
    (fun b hb => Ideal.Quotient.eq_zero_iff_mem.2 (hqp (hϖ (Ideal.mem_map_of_mem _ hb))))
  have h1 : ∀ u m (t : Dec (F := T.F) (T.pl u)), κ u m t = 1 ↔ X.ψ u m t - 1 ∈ p := fun u m t => by
    rw [← Units.val_eq_one, (hκ u m).1, ← Ideal.Quotient.eq, map_one]
  have hpin : ∀ u m, (∀ k, X.ψ u m (s u k) - 1 ∈ p) → ∀ t ∈ I u, κ u m t = 1 := fun u m hk =>
    hsP u _ h0 (κ u m) (hκ u m).2.1 (fun t ht => ((hκ u m).2.2 t ht).1) (by
      rintro _ ⟨k, rfl⟩; exact (h1 _ _ _).2 (hk k))
  have hA : ∀ u, ∀ t ∈ I u, κ u a t = 1 := fun u => hpin u a fun k => hx (.inl (u, k))
  have hE : ∀ t ∈ I v, κ v i t = κ v j t := by
    refine hP0.eq h0 _ _ (hκ v i).2.1 (hκ v j).2.1 (fun t ht => ((hκ v i).2.2 t ht).1)
      (fun t ht => ((hκ v j).2.2 t ht).1) fun t ht => Units.ext ?_
    rw [(hκ v i).1, (hκ v j).1, Ideal.Quotient.eq]
    rcases ht with rfl | ⟨ht, ht'⟩
    · exact hx (.inr (.inr ()))
    · exact hqp (hU t ⟨ht, ht', hOk.ineL _ (T.ovl v) _ ht⟩)
  have hI : ∀ u, ∀ t ∈ I u, κ u i t = 1 := fun u => by
    by_cases hu : u = v
    · subst hu
      intro t ht
      rcases ha with rfl | rfl
      · exact (hE t ht).trans (hA u t ht)
      · have h2 := (hκ u i).2.2 t ht
        refine Units.val_eq_one.1 (eq_one_of_pow h0 h2.1 two_ne_zero ?_)
        rw [← Units.val_pow_eq_pow_val, sq, Units.val_eq_one]
        rw [← hE t ht] at h2
        exact h2.2
    · exact hpin u i fun k => hx (.inr (.inl (⟨u, hu⟩, k)))
  have hall : ∀ u m, ∀ t ∈ I u, κ u m t = 1 := fun u m t ht => by
    rcases ha' m with rfl | rfl | rfl | rfl
    · exact hA u t ht
    · simpa [hA u t ht] using ((hκ u a).2.2 t ht).2
    · exact hI u t ht
    · simpa [hI u t ht] using ((hκ u i).2.2 t ht).2
  obtain ⟨n, hn⟩ := hPM.fin
  refine hp.le_of_pow_le (n := n) (hn.trans (sup_le (sup_le (hJ.trans hqp) (hϖ.trans hqp)) (Ideal.span_le.2 ?_)))
  rintro _ ⟨u, m, t, ht, rfl⟩
  exact (h1 u m ⟨t, Ine_le_Dec _ ht⟩).1 (hall u m _ ht)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OpRelOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem relOf_act {T W κ : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (t : κ → T) :
    ∃ act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W, ∀ a, act (MvPolynomial.X a) = θ (t a) :=
  ⟨(MonoidAlgebra.lift ℂ (Module.End ℂ W) T ((Units.coeHom _).comp θ)).comp
    (MvPolynomial.aeval fun a => MonoidAlgebra.single (t a) 1), fun a => by simp⟩
private theorem relOf_int {R W W' κ S : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module ℂ W']
    [CommRing S] [Algebra ℂ S] (c : R →+* ℂ) (v : κ → S)
    (act : MvPolynomial κ R →ₐ[R] Module.End R W) (act' : S →ₐ[ℂ] Module.End ℂ W') (g : W →+ W')
    (hg : ∀ r m, g (r • m) = c r • g m)
    (h : ∀ a m, act' (v a) (g m) = g (act (MvPolynomial.X a) m)) (F : MvPolynomial κ R) (m : W) :
    act' (MvPolynomial.eval₂Hom ((algebraMap ℂ S).comp c) v F) (g m) = g (act F m) := by
  induction F using MvPolynomial.induction_on generalizing m with
  | C r =>
    rw [MvPolynomial.eval₂Hom_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, RingHom.comp_apply, AlgHom.commutes]
    simp [hg]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  | mul_X p a hp =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, MvPolynomial.eval₂Hom_X', h, hp]
private theorem relOf_uy {R W W' ι S : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module ℂ W']
    [CommRing S] [Algebra R S] (c : R →+* ℂ) (act : S →ₐ[R] Module.End R W)
    (act' : MvPolynomial (ι ⊕ ι) ℂ →ₐ[ℂ] Module.End ℂ W') (g : W →+ W') (hg : ∀ r m, g (r • m) = c r • g m)
    (ψ : MvPolynomial (ι ⊕ ι) R →ₐ[R] S) (N : ℕ) (e : ι → ℕ) (E : ι ⊕ ι → Module.End R W)
    (hu : ∀ i, act (ψ (MvPolynomial.X (.inl i))) = (N : R) ^ e i • E (.inl i))
    (hy : ∀ i, act (1 + ψ (MvPolynomial.X (.inr i))) = E (.inr i))
    (h : ∀ a m, act' (MvPolynomial.X a) (g m) = g (E a m)) (F : MvPolynomial (ι ⊕ ι) R) (k : ℕ)
    (h0 : act' (MvPolynomial.eval₂Hom ((algebraMap ℂ (MvPolynomial (ι ⊕ ι) ℂ)).comp c)
      (Sum.elim (fun i => ((N : ℂ) ^ e i) • MvPolynomial.X (.inl i)) fun i => MvPolynomial.X (.inr i) - 1) F ^ k) = 0) (m : W) :
    g (act (ψ F ^ k) m) = 0 := by
  have h1 := relOf_int c (Sum.elim (fun i => ((N : ℂ) ^ e i) • MvPolynomial.X (.inl i)) fun i => MvPolynomial.X (.inr i) - 1)
    (act.comp ψ) act' g hg (fun a m => by
      rw [AlgHom.comp_apply]
      rcases a with i | i
      · rw [Sum.elim_inl, hu, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hg, map_pow, map_natCast, h]
      · have e := hy i
        rw [map_add (f := _), map_one] at e
        rw [Sum.elim_inr, eq_sub_of_add_eq' e, map_sub, map_one, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h]
        rfl) (F ^ k) m
  rw [map_pow, h0, AlgHom.comp_apply, map_pow] at h1
  exact h1.symm
theorem UpperTheory.V.Th.relOfX_alt :
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (T : ThData l A.ρ x δ) (ι : Qbar l ≃+* ℂ), (∀ m : A.P, (∀ y : _root_.UpperTheory.V.Pa.LevPtAlt A ι, y.sp m = 0) → m = 0) → ∀ (j : Fin q) (F : MvPolynomial (Fin n ⊕ Fin n) A.R), (∀ (y : _root_.UpperTheory.V.Pa.LevPtAlt A ι) θ, IsTheta (y.σ j).ρ (ellC l _) θ → ∀ χ : (Fin n → ((w j).adicCompletion L)ˣ) →* ℂˣ, (⨅ t, Module.End.maxGenEigenspace (θ t).val (χ t : ℂ)) ≠ ⊥ → ∀ (S : Type) [CommRing S] [Algebra ℂ S] (U : Fin n → S), (∀ i : Fin n, (U i - algebraMap ℂ S ((qj w j : ℂ) ^ (i : ℕ) * (χ (Pi.mulSingle i (x j)) : ℂ))) ^ n.factorial = 0) → MvPolynomial.eval₂ ((algebraMap ℂ S).comp (ι.toRingHom.comp y.θ)) (Sum.elim U fun i => algebraMap ℂ S (χ (Pi.mulSingle i (δ j)) : ℂ) - 1) F = 0) → T.act1 (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i)) F) = 0 := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ _ _ hδ T ι hsep j F hF
  rw [← pow_one (MvPolynomial.rename _ F)]
  refine LinearMap.ext fun m => Subtype.ext (hsep _ fun y => ?_)
  obtain ⟨Θ, hΘ⟩ := thetaQ L n q w ℂ y.Y y.π (fun _ => ellC l _) fun j =>
    (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[(w j).adicCompletion L])).ne').isUnit
  let t : Fin n ⊕ Fin n → Fin n → ((w j).adicCompletion L)ˣ :=
    Sum.elim (fun i => Pi.mulSingle i (x j)) fun i => Pi.mulSingle i (δ j)
  obtain ⟨act, hact⟩ := relOf_act (Θ j) t
  let c : A.R →+* ℂ := ι.toRingHom.comp y.θ
  let v : Fin n ⊕ Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ :=
    Sum.elim (fun i => ((qj w j : ℂ) ^ (i : ℕ)) • MvPolynomial.X (.inl i)) fun i => MvPolynomial.X (.inr i) - 1
  let g : fixd A.ρ (UC n w fun _ => ellC l _) →+ fixd y.π (UC n w fun _ => ellC l _) :=
    { toFun := fun m => ⟨y.sp m, fun u hu => by rw [← y.sp_act, m.2 u hu]⟩
      map_zero' := Subtype.ext (map_zero y.sp)
      map_add' := fun a a' => Subtype.ext (map_add y.sp _ _) }
  have hg : ∀ (r : A.R) m, g (r • m) = c r • g m := fun r m => Subtype.ext (y.sp_smul r m)
  have hΘg : ∀ t m, (Θ j t).val (g m) = g ((T.Θ1 j t).val m) := fun t m =>
    Subtype.ext (thetaMap L n q w A.R A.P ℂ y.Y A.ρ y.π _ T.Θ1 Θ T.h1 hΘ y.sp y.sp_act j t m (g m) rfl)
  have h0 := nilKillX hP.gl hP.bz L n q w y.Y y.π _ Θ hΘ j (y.σ j) (y.iso j) _ t (fun i => ⟨_, _, i, hδ j, rfl⟩) act hact
    (MvPolynomial.eval₂Hom ((algebraMap ℂ _).comp c) v F) (fun θ hθ χ hχ S _ _ φ h1 h2 => by
      refine Eq.trans ?_ (hF y θ hθ χ hχ S (fun i => ((qj w j : ℂ) ^ (i : ℕ)) • φ (MvPolynomial.X (.inl i))) fun i => ?_)
      · rw [MvPolynomial.coe_eval₂Hom]
        refine (MvPolynomial.eval₂_comp_left φ.toRingHom _ _ _).trans ?_
        congr 1
        · ext r
          exact φ.commutes _
        · funext a
          rcases a with i | i
          · exact map_smul φ _ _
          · exact (map_sub φ _ _).trans (by rw [h2, map_one]; rfl)
      · rw [map_mul, Algebra.smul_def, ← mul_sub, mul_pow]
        exact mul_eq_zero_of_right _ (h1 i))
  rw [← pow_one (MvPolynomial.eval₂Hom _ v F)] at h0
  exact congrArg Subtype.val (relOf_uy c T.act1 act g hg
    (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i))) (qj w j) (fun i => (i : ℕ))
    (fun a => (T.Θ1 j (t a)).val)
    (fun i => by rw [MvPolynomial.rename_X]; exact T.act_uVariable_eq_pow j i)
    (fun i => by rw [MvPolynomial.rename_X]; exact T.act_yVariable j i)
    (fun a m => by rw [hact]; exact hΘg _ m) F _ h0 m)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdDefs
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.Ord
section At
variable {F Ω : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {n : ℕ} (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
end At
def AutYAlt {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l}
    (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ)
    (P : ∀ (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), H.PartAltAlt ι lam ξ → Prop) : Prop :=
  ∀ lam ∈ H.admitted, ∀ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), IsAlgWt ι lam ξ → ∀ F ∈ H.Big ι ξ,
    (∃ K, F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K)) → (∃ e, F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e)) →
    F ∈ ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y}, Y.1.Y
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ) (J : Ideal B.B)
end U
def OrdScalAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
      (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (Y : H.PartAltAlt ι lam ξ) (K : H.Lev) (e : ℕ), c0 ≤ e → ∀ F ∈ Y.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K e, F ≠ 0 →
    ∀ (v : H.V) (b : Fin n → ℂ), (∀ j, b j ≠ 0 ∧ H.opC ι lam d (.inr (v, j)) F = b j • F) →
      ∃ ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsSubquotient (Y.σl v).ρ (PS ω) ∧
        (∀ i (y : Uo ((H.Sl v).adicCompletion L)), (ω i y : ℂ) * ι (H.finPart θ x.toRingHom lam v i y) = 1) ∧
        ∀ j : Fin n, b j = (H.lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)
def PartPtAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) P, _root_.UpperTheory.V.Z.Ord.AutYAlt H ι P →
    ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
      (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → lam ∈ H.admitted →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] (y : H.TK θ a K →ₐ[c.O] Qbar l),
      y.toRingHom.comp (algebraMap A _) = x.toRingHom → ∃ (Y : H.PartAltAlt ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d),
        P lam d ξ Y ∧ F ≠ 0 ∧ F ∈ Y.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K c0 ∧ ∀ i, H.opC ι lam d i F = ι (y (H.gen θ a K i)) • F
def CoreOrdAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) P, _root_.UpperTheory.V.Z.Ord.AutYAlt H ι P → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))]
      [Alg.IsCO c.O (H.TK θ a K)] (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ),
      H.IsUniv θ a K (maximalIdeal _) D ψ → ∀ lam ∈ H.admitted, ∀ y : H.TK θ a K →ₐ[c.O] Qbar l,
      H.Arith θ (y.toRingHom.comp (algebraMap A _)) lam →
      ∃ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.PartAltAlt ι lam ξ), P lam d ξ Y ∧ D.map y.toRingHom = W.GDet.ofRep (W.mat Y.r) ∧
        ∀ v, ∃ ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, IsSubquotient (Y.σl v).ρ (PS ω) ∧
          ∀ i, OrdChar ι (H.art v) (ω i) (htW lam i) (W.pushCh y.toRingHom (ψ v i))
def AutUOAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ)
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ → _root_.UpperTheory.V.Z.Ord.AutYAlt (hset Q τ₀) ι fun _ _ _ Y =>
      Af.IsIrr (Y.r.comp V.pr) → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧
        Af.AttC ι (Y.r.comp V.pr) π ∧ ∀ v, π.IsLocComp ((hset Q τ₀).Sl v) (Y.σl v)
def EndOrdAlt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), ∀ J : Ideal B.B, R.IsJ B K J → ENDO B ι J
end UpperTheory.V.Z.Ord
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartRep
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
def Ord1Alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) W),
    GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → ∀ (b : ℕ) (φ : Fin n → Uo k → ℂ) (μ : Fin n → ℂ),
    (∀ i (y : Uo k), (y : kˣ) ∈ Uc k (b + 1) → φ i y = 1) → Reg k μ → Module.rank ℂ (locEig π b φ μ) ≤ 1
def SphSameAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) → ∀ σ σ', IsAutRepU σ → IsAutRepU σ' →
    (∀ w, IsSplitAt w → ∃ τ, Cp σ w τ ∧ Cp σ' w τ) → YOf Q ι τ₀ e ξ σ ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ →
    YOf Q ι τ₀ e ξ σ' ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev = YOf Q ι τ₀ e ξ σ' ⊓ zL (hset Q τ₀) θ ι x.toRingHom lam c0 ev d ((hset Q τ₀).X.rpF ℂ d m)
def AtSameAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), ∀ σ σ', IsAutRepU σ → IsAutRepU σ' → YOf Q ι τ₀ e ξ σ ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ →
    YOf Q ι τ₀ e ξ σ' ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → ∀ π : CuspSub L n, At π σ → At π σ'
def BcOfAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.BCT.Unr E →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
    ∀ ρ : G E Ω →* GL (Fin n) (Qbar l), Continuous ρ → Af.IsIrr ρ →
    (∀ᶠ w : Plc E in cofinite, IsSplitAt w → ∀ τ, Cp σ w τ → _root_.UpperTheory.V.Z.Win.LocGlobT ι ρ w τ) →
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ At π σ ∧
      (∀ φ lam, HasWeightAt σ φ lam → π.HasInfChar φ (infOfWeight lam)) ∧ ∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B
def PartRepAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → ∀ (K : H.Lev) (a : H.Op → c.O) [Fact (CommOn (H.MK θ a K) (H.op A))] [Module.Free A (H.MK θ a K)] [Module.Finite A (H.MK θ a K)]
    (z : H.TK θ a K →ₐ[c.O] Qbar l), z.toRingHom.comp (algebraMap A _) = x.toRingHom → ∀ (I : Ideal (H.TK θ a K)) (D : W.GDet n (H.TK θ a K) H.Gq)
    (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K I D ψ → ∀ ρ : H.Gq →* GL (Fin n) (Qbar l), Continuous ρ →
    Af.IsIrr ρ → D.map z.toRingHom = W.GDet.ofRep (W.mat ρ) → ∀ Y : H.PartAltAlt ι lam ξ,
    Y.Y ⊓ zPart H θ ι x.toRingHom lam ξ K c0 (fun i => ι (z (H.gen θ a K i))) ≠ ⊥ → ∃ g : GL (Fin n) (Qbar l), ∀ h, Y.r h = g * ρ h * g⁻¹
end UpperTheory.V.Z.J.D
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PromodularityCaseThree
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace UpperTheory.V.Cu
section
variable {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R)
end
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
end
def SeedIVAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D),
    Ctx3 D → T₀.Ok → Four T₀ → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l),
    ∃ (w : ℕ) (s : PD T₀.ι (G T₀.F Ω) 𝔞.k), w.Prime ∧ T₀.Splits w ∧ (T₀.fr {w}).IsRes (𝔞.red c) s ∧ Supp nM s.r ∧
      ∀ (T : Tower D) (hT : T₀.Le T), T.Ok → Dies l w T.F →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧ T₀.OverT hT s (Q.map (𝔞.red c₁)) ∧
          InA (Q.map (𝔞.red c₁)) ∧ Ent (Q.map (𝔞.red c₁)).r (-wBe) ∧ Ent (Q.map (𝔞.red c₁)).r (-wTh)
def ChainRankFour : Prop :=
  CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O)
    (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PotentialModularityTower ι X J → ∀ C : ℕ, (T.fr ∅).Bounds ((residue c'.O).comp (inc h)) T.d C →
    30 * (C + 1) * (C + 1) ≤ T.d → ∀ x : X.A →ₐ[c'.O] ResidueField c'.O,
      (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      Good4 (T.fr ∅) ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x)
def RankFourChainReductionDense : Prop :=
  CohomologyHyp → HFit → _root_.UpperTheory.V.Cu.SeedIVAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx3 D → T₀.Ok → Four T₀ → TameL l T₀.F →
    ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' →
            Chain4 (T.fr ∅) (𝔞.red c) c₀' (Q.map (𝔞.red c₁))
def PromodularityCaseThreeDense : Prop :=
  CohomologyHyp → UpperTheory.V.Published.FerreroWashington → HFit → _root_.UpperTheory.V.Cu.SeedIVAlt → _root_.UpperTheory.V.Ws.PMExAlt → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D →
    ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) → _root_.UpperTheory.V.Ws.ProModAlt D ι 𝔞 r
def AutomorphyRankFourDense : Prop :=
  CohomologyHyp → UpperTheory.V.Published.FerreroWashington → HFit → _root_.UpperTheory.V.Ws.SeedIIAlt → _root_.UpperTheory.V.Cu.SeedIVAlt → _root_.UpperTheory.V.Ws.PMExAlt → _root_.UpperTheory.V.Aut.SymplecticFourImageDense
end UpperTheory.V.Cu
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ResEq2
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Z.J.D
private def resEquiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (K : Subgroup G) (e : ρ.Equiv ρ') :
    Representation.Equiv (ρ.comp K.subtype) (ρ'.comp K.subtype) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v =>
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (g : G) v
theorem resEq2_alt : _root_.UpperTheory.V.Z.J.D.TypePS2Alt → PsRes → _root_.UpperTheory.V.Z.J.D.ResidualEqualityRankTwo := by
  intro hT hP hN L Ω _ _ _ _ _ _ n hn π π' w A h τ τ' hτ hτ' χ hx hc hc'
  obtain ⟨ω, hs, ⟨e⟩, hω⟩ := hT hN L Ω n hn π w A h τ hτ χ hx hc
  obtain ⟨ω', hs', ⟨e'⟩, hω'⟩ := hT hN L Ω n hn π' w A h τ' hτ' χ hx hc'
  have ha : IsLocalArtin h (artOf h) := Classical.epsilon_spec (_root_.UpperTheory.V.Z.Win.T2.laArtinLit' hN h)
  have hu : ∀ i (y : Uo (w.adicCompletion L)), ω i y = ω' i y := by
    intro i y
    obtain ⟨σ, hσ⟩ := ha.surj y
    have h1 : valuation (w.adicCompletion L) (artOf h σ : w.adicCompletion L) = 1 := by
      rw [hσ]
      exact y.2
    have h2 := ha.ord_eq σ
    rw [GlobalTheory.SmGL.ord_eq_zero_iff.2 h1] at h2
    have hI : (σ : G L Ω) ∈ Ine (F := L) A := deg_eq_zero_iff.mp (by omega)
    have e1 : artOf h (ineIncl h ⟨σ, hI⟩) = y := hσ
    have h3 := hω i ⟨σ, hI⟩
    have h4 := hω' i ⟨σ, hI⟩
    rw [e1] at h3 h4
    exact h3.trans h4.symm
  obtain ⟨f⟩ := hP (w.adicCompletion L) n ω ω' hs hs' hu
  exact ⟨(resEquiv _ e).trans (f.trans (resEquiv _ e').symm)⟩
end UpperTheory.V.Z.J.D
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SeedRes
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace UpperTheory.V.Ws.Chn
section Abs
variable {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] {Φ : Fr O Γ} {a : O →+* k}
end Abs
section In
variable {ι Γ R : Type} [Group Γ] [CommRing R] {P P' : PD ι Γ R}
end In
section Map
variable {O Γ R R' : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing R'] {Φ : Fr O Γ} {a : O →+* R}
end Map
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
theorem seed_res_alt (T : Tower D) (𝔞 : Amb l) {ι : PadicAlgCl l ≃+* ℂ} {c₁ : Coef l} {h : c.O ≤ c₁.O}
    {Q : PD T.ι (G T.F Ω) c₁.O} (hQ : T.SeedPairAlt ι h Q) : (T.fr ∅).IsRes (𝔞.red c) (Q.map (𝔞.red c₁)) := by
  have h1 : (T.fr ∅).IsRes ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O)) := by
    refine ⟨pair_map hQ.pair _, hQ.res, fun i j n => ?_⟩
    have h2 := (hQ.cont i j 1).comp (Ideal.Quotient.lift (maximalIdeal c₁.O ^ 1) (residue c₁.O)
      fun x hx => (residue_eq_zero_iff x).2 (by rwa [pow_one] at hx))
    exact h2.comp (Ideal.Quotient.mk ((⊥ : Ideal (ResidueField c₁.O)) ^ n))
  have h2 := (chainMap (T.fr ∅) _ (𝔞.j c₁) _).1.2 h1
  have e1 : (𝔞.j c₁).comp ((residue c₁.O).comp (inc h)) = 𝔞.red c :=
    RingHom.ext fun x => congrArg (residue 𝔞.V) (𝔞.compat c c₁ h x)
  rw [e1] at h2
  exact h2
end Gal
end UpperTheory.V.Ws.Chn
end
end

