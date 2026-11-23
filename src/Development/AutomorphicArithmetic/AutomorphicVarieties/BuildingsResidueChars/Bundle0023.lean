module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EqOneOfIrreduciblePiAbelianFixedNeBot
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.eq_one_of_irreducible_pi_abelian_fixed_ne_bot :
    ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)], (∀ a (x y : Γ a), x * y = y * x) →
    ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (∀ a, Γ a) Y) (H : ∀ a, Subgroup (Γ a)), τ.IsIrreducible →
    (∀ a, fixed (τ.comp (MonoidHom.mulSingle Γ a) : Representation ℂ (Γ a) Y) (H a) ≠ ⊥) → ∀ g : ∀ a, Γ a, (∀ a, g a ∈ H a) → τ g = 1 := by
  intro α _ _ Γ _ hcomm Y _ _ τ H hirr hne g hg
  have hfixall : ∀ a (h : H a) (y : Y), τ (Pi.mulSingle a (h : Γ a)) y = y := by
    intro a
    have hc : ∀ (x : Γ a) (g' : ∀ b, Γ b), Pi.mulSingle a x * g' = g' * Pi.mulSingle a x := by
      intro x g'
      funext b
      simp only [Pi.mul_apply]
      exact hcomm b _ _
    let R : Subrepresentation τ :=
      { toSubmodule := fixed (τ.comp (MonoidHom.mulSingle Γ a) : Representation ℂ (Γ a) Y) (H a)
        apply_mem_toSubmodule := by
          intro g' y hy h
          have hy' := hy h
          simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply,
            MonoidHom.mulSingle_apply] at hy' ⊢
          rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hy'] }
    have hR : R = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top R with h | h
      · exfalso
        apply hne a
        have := congrArg Subrepresentation.toSubmodule h
        exact this
      · exact h
    intro h y
    have hy : y ∈ R.toSubmodule := by
      rw [hR]
      exact Submodule.mem_top
    have := hy h
    simpa using this
  letI : ∀ a, CommGroup (Γ a) := fun a => { (inferInstance : Group (Γ a)) with mul_comm := hcomm a }
  have hs : ∀ (s : Finset α) (y : Y), τ (∏ a ∈ s, Pi.mulSingle a (g a)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y
      rw [Finset.prod_empty, map_one, Module.End.one_apply]
    | insert a s ha ih =>
      intro y
      rw [Finset.prod_insert ha, map_mul, Module.End.mul_apply, ih]
      exact hfixall a ⟨g a, hg a⟩ y
  have hg' : g = ∏ a, Pi.mulSingle a (g a) := (Finset.univ_prod_mulSingle g).symm
  ext y
  rw [Module.End.one_apply]
  conv_lhs => rw [hg']
  exact hs Finset.univ y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRefinementBlockOrder
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

private theorem exists_equiv_sigma_blk_lt_iff_lt {N : ℕ} {β : Type} [LinearOrder β] (κ : Fin N → β) :
    ∃ (t : ℕ) (c : Fin t → ℕ) (f : (Σ a, Fin (c a)) ≃ Fin N), ∀ p q, blk f p < blk f q ↔ κ p < κ q := by
  classical
  let S : Finset β := Finset.univ.image κ
  let o : Fin S.card ≃o S := S.orderIsoOfFin rfl
  have hS : ∀ p, κ p ∈ S := fun p => Finset.mem_image_of_mem κ (Finset.mem_univ p)
  let g : Fin N → Fin S.card := fun p => o.symm ⟨κ p, hS p⟩
  refine ⟨S.card, fun a => Fintype.card {p // g p = a},
    (Equiv.sigmaCongrRight (fun a => (Fintype.equivFin {p // g p = a}).symm)).trans
      (Equiv.sigmaFiberEquiv g), ?_⟩
  intro p q
  have hb : ∀ x, blk ((Equiv.sigmaCongrRight (fun a => (Fintype.equivFin {p // g p = a}).symm)).trans
      (Equiv.sigmaFiberEquiv g)) x = g x := by
    intro x
    rfl
  rw [hb, hb]
  show o.symm ⟨κ p, hS p⟩ < o.symm ⟨κ q, hS q⟩ ↔ κ p < κ q
  rw [OrderIso.lt_iff_lt]
  exact Subtype.mk_lt_mk

theorem UpperTheory.exists_refinement_block_order :
    ∀ (N : ℕ) (r s : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N) (j : Fin r) (d' : Fin s → ℕ) (e' : (Σ b, Fin (d' b)) ≃ Fin (d j)),
    ∃ (t : ℕ) (c : Fin t → ℕ) (f : (Σ a, Fin (c a)) ≃ Fin N), ∀ p q, blk f p < blk f q ↔ (blk e p < blk e q ∨ ∃ p' q', p = e ⟨j, p'⟩ ∧ q = e ⟨j, q'⟩ ∧ blk e' p' < blk e' q') := by
  intro N r s d e j d' e'
  classical
  obtain ⟨K, hK⟩ : ∃ K : (Σ a, Fin (d a)) → Lex (ℕ × ℕ), ∀ x y, K x < K y ↔
      (x.1 < y.1 ∨ ∃ p' q', x = ⟨j, p'⟩ ∧ y = ⟨j, q'⟩ ∧ blk e' p' < blk e' q') := by
    refine ⟨fun x => toLex ((x.1 : ℕ), if h : x.1 = j then ((blk e' (h ▸ x.2) : Fin s) : ℕ) else 0), ?_⟩
    rintro ⟨a, u⟩ ⟨b, w⟩
    show toLex ((a : ℕ), if h : a = j then ((blk e' (h ▸ u) : Fin s) : ℕ) else 0) <
        toLex ((b : ℕ), if h : b = j then ((blk e' (h ▸ w) : Fin s) : ℕ) else 0) ↔ _
    rw [Prod.Lex.toLex_lt_toLex]
    by_cases ha : a = j <;> by_cases hb : b = j
    · subst ha
      subst hb
      rw [dite_eq_left rfl, dite_eq_left rfl]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact absurd h (lt_irrefl _)
        · exact Or.inr ⟨u, w, rfl, rfl, Fin.lt_iff_val_lt_val.mpr h⟩
      · rintro (h | ⟨p', q', h1, h2, h3⟩)
        · exact absurd h (lt_irrefl _)
        · refine Or.inr ⟨rfl, ?_⟩
          rw [Sigma.mk.inj_iff] at h1 h2
          rw [eq_of_heq h1.2, eq_of_heq h2.2]
          exact Fin.lt_iff_val_lt_val.mp h3
    · subst ha
      rw [dite_eq_left rfl, dite_eq_right hb]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mpr h)
        · exact absurd h (Nat.not_lt_zero _)
      · rintro (h | ⟨p', q', -, h2, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mp h)
        · exact absurd (congrArg Sigma.fst h2) hb
    · subst hb
      rw [dite_eq_right ha, dite_eq_left rfl]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mpr h)
        · exact absurd (Fin.ext h) ha
      · rintro (h | ⟨p', q', h1, -, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mp h)
        · exact absurd (congrArg Sigma.fst h1) ha
    · rw [dite_eq_right ha, dite_eq_right hb]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mpr h)
        · exact absurd h (lt_irrefl 0)
      · rintro (h | ⟨p', q', h1, -, -⟩)
        · exact Or.inl (Fin.lt_iff_val_lt_val.mp h)
        · exact absurd (congrArg Sigma.fst h1) ha
  obtain ⟨t, c, f, hf⟩ := exists_equiv_sigma_blk_lt_iff_lt (fun p : Fin N => K (e.symm p))
  refine ⟨t, c, f, fun p q => ?_⟩
  rw [hf, hK]
  simp only [Equiv.symm_apply_eq]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def extL (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n) :
    archLie K a →ₗ[ℝ] archLie K n where
  toFun Y := (isExpLieAlgebra K n).ofLie (toLie K n (ext0 e (mat Y.1)))
  map_add' X Y := Subtype.ext (matrixExtendByZero_add e (mat X.1) (mat Y.1))
  map_smul' c X := Subtype.ext (by
    change ext0 e (c • mat X.1) = c • ext0 e (mat X.1)
    simp only [ext0, Matrix.mul_smul, Matrix.smul_mul])

private theorem key (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n)
    (g : AdelicGLn.AdelicGL K n) (ψ : AdelicGLn.AdelicGL K n → ℂ) (m : AdelicGLn.AdelicGL K a) (x : archGroup K a)
    (Y : archLie K a) :
    archSlice (fun m => ψ (g * emb e m)) m (x * (isExpLieAlgebra K a).expG Y) =
      archSlice ψ (g * emb e m) (embArch e x * (isExpLieAlgebra K n).expG (extL K e Y)) := by
  obtain ⟨h1, h2⟩ := UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e
  have h3 : embArch e ((isExpLieAlgebra K a).expG Y) = (isExpLieAlgebra K n).expG (extL K e Y) := h2 (mat Y.1)
  rw [← h3, ← map_mul, archSlice_apply, archSlice_apply, ← h1, map_mul (emb e) m, mul_assoc]

theorem UpperTheory.exists_restriction_blockEmbedding_intertwines_lie :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (g : AdelicGLn.AdelicGL K n), ∃ f : archSmooth K n →ₗ[ℂ] archSmooth K a, (∀ ψ m, (f ψ).1 m = ψ.1 (g * emb e m)) ∧ ∀ X ψ, f (lam K n (ext0 e X) ψ) = lam K a X (f ψ) := by
  intro K _ _ a n e g
  have hs : ∀ ψ : archSmooth K n, (fun m => ψ.1 (g * emb e m)) ∈ archSmooth K a := fun ψ m => by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro x
    simp only [key]
    exact (((isExpLieAlgebra K n).isSmoothFun_iff).1 (ψ.2 (g * emb e m)) (embArch e x)).comp
      (LinearMap.toContinuousLinearMap (extL K e)).contDiff
  refine ⟨{ toFun := fun ψ => ⟨_, hs ψ⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun _ _ => rfl, fun X ψ => Subtype.ext (funext fun m => ?_)⟩
  have h1 := (isExpLieAlgebra K a).hasDerivAt_rightDeriv (hs ψ m) ((isExpLieAlgebra K a).ofLie (toLie K a X)) 1
  have h2 := (isExpLieAlgebra K n).hasDerivAt_rightDeriv (ψ.2 (g * emb e m))
    (extL K e ((isExpLieAlgebra K a).ofLie (toLie K a X))) 1
  simp only [key, map_one, map_smul] at h1
  exact (uAction_ι_apply (toLie K n (ext0 e X)) ψ (g * emb e m)).trans
    ((h2.unique h1).trans (uAction_ι_apply (toLie K a X) ⟨_, hs ψ⟩ m).symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSlSpReduction
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aux {G H G' H' : Type} [Monoid G] [Monoid H] [Monoid G'] [Monoid H'] (E : G →* H) (i : G' → G) (i' : H' → H)
    (j : G' → H') (hj : ∀ k k', j (k * k') = j k * j k') (hi : ∀ k, E (i k) = i' (j k)) (V : Submodule ℂ (H' → ℂ))
    (hst : ∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) :
    (∀ f ∈ V.map (LinearMap.funLeft ℂ ℂ j), ∀ k', (fun k => f (k * k')) ∈ V.map (LinearMap.funLeft ℂ ℂ j)) ∧
    ∀ (f : G → ℂ) (ψ : H → ℂ) (g₀ : H), (∀ g, (fun k => ψ (g * i' k)) ∈ V) → (∀ m, f m = ψ (g₀ * E m)) →
      ∀ g, (fun k => f (g * i k)) ∈ V.map (LinearMap.funLeft ℂ ℂ j) := by
  constructor
  · rintro _ ⟨f, hf, rfl⟩ k'
    refine ⟨_, hst f hf (j k'), funext fun k => ?_⟩
    simp only [LinearMap.funLeft_apply, hj]
  · intro f ψ g₀ hψ hf g
    refine ⟨_, hψ (g₀ * E g), funext fun k => ?_⟩
    simp only [LinearMap.funLeft_apply]
    rw [hf, map_mul, hi, mul_assoc]

private theorem aux2 (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (k : archCompact K a) :
    embArch e k.1 ∈ archCompact K n := by
  have h := UpperTheory.blockEmbedding_adelic_norm_compat K a n e _ (Subgroup.mem_comap.1 k.2)
  rw [(UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e).1] at h
  exact Subgroup.mem_comap.2 h

private theorem aux3 {G X : Type} (A : Submodule ℂ (G → ℂ)) (s : Set A) (p : X → G) (W : Submodule ℂ (X → ℂ))
    (h : ∀ f ∈ s, (fun k => f.1 (p k)) ∈ W) : ∀ f ∈ Submodule.span ℂ s, (fun k => f.1 (p k)) ∈ W := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    convert W.zero_mem using 1
  | add x y _ _ hx hy =>
    convert W.add_mem hx hy using 1
  | smul c x _ hx =>
    convert W.smul_mem c hx using 1

theorem UpperTheory.finiteDimensional_slSp_reduction :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S : Submodule ℂ (archSmooth K n)), Types S → Types (slSp e Γ S) := by
  intro K _ _ a n e Γ S hS
  obtain ⟨V, hVf, hVst, hV⟩ := hS
  let j : archCompact K a → archCompact K n := fun k => ⟨embArch e k.1, aux2 K a n e k⟩
  have hj : ∀ k k', j (k * k') = j k * j k' := fun k k' => Subtype.ext (map_mul (embArch e) k.1 k'.1)
  have hi : ∀ k : archCompact K a, emb e (infEmb K a k.1) = infEmb K n (j k).1 :=
    fun k => (UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e).1 k.1
  have key := aux (G := AdelicGLn.AdelicGL K a) (H := AdelicGLn.AdelicGL K n) (emb e)
    (fun k : archCompact K a => infEmb K a k.1)
    (fun k : archCompact K n => infEmb K n k.1) j hj hi V hVst
  refine ⟨V.map (LinearMap.funLeft ℂ ℂ j), ?_, key.1, ?_⟩
  · exact Module.Finite.map V _
  · intro f hf g
    unfold slSp at hf
    refine aux3 (archSmooth K a) _ (fun k : archCompact K a => g * infEmb K a k.1)
      (V.map (LinearMap.funLeft ℂ ℂ j)) ?_ f hf
    rintro f' ⟨ψ, hψ, g₀, -, hf'⟩
    exact key.2 f'.1 ψ.1 g₀ (hV ψ hψ) hf' g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedNeBotOfIsSubquotientOfIsCompact
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G V) (π : Representation ℂ G W) (H : Subgroup G), IsSmooth π → IsSubquotient σ π → IsCompact (H : Set G) →
    fixed σ H ≠ ⊥ → fixed π H ≠ ⊥ := by
  intro G _ _ _ V W _ _ _ _ σ π H hπ hsq hH hne
  obtain ⟨S, f, hf⟩ := hsq
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g : G | S.toRepresentation g v = v} = {g : G | π g v = v} := by
      ext g; exact Subtype.ext_iff
    rw [this]; exact hπ v
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨u, rfl⟩ := hf x
  obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hS hH f.toLinearMap u fun h hh => by
    show f (S.toRepresentation h u) = f u
    rw [f.isIntertwining]
    simpa using hx ⟨h, hh⟩
  refine (Submodule.ne_bot_iff _).2 ⟨v.1, fun h => ?_, fun h0 => hx0 ?_⟩
  · exact congrArg Subtype.val (hv h)
  · have hv0 : v = 0 := Subtype.ext h0
    have e' : f.toLinearMap v = f u := e
    rw [← e', hv0, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelNontrivialOfBlocksLeOne
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_borel_nontrivial_of_blocks_le_one :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N), (∀ a, d a ≤ 1) → Nontrivial (Jacquet π (unipRad k e)) →
    Nontrivial (Jacquet π (unipB k (Fin N))) := by
  intro k _ _ _ _ N V _ _ π r d e hd hR
  have hinj : Function.Injective (blk e) := by
    intro i j hij
    apply e.symm.injective
    simp only [GlobalTheory.SmGL.blk] at hij
    revert hij
    generalize e.symm i = p
    generalize e.symm j = q
    intro hij
    obtain ⟨a, x⟩ := p
    obtain ⟨b, y⟩ := q
    simp only at hij
    subst hij
    have hxy : x = y := by
      have h1 := x.isLt
      have h2 := y.isLt
      have h3 := hd a
      ext
      omega
    rw [hxy]
  set S : Finset (Fin r) := Finset.univ.image (blk e) with hSdef
  have hS : S.card = N := by
    rw [hSdef, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  let f : Fin N → Fin N := fun i =>
    (S.orderIsoOfFin hS).symm ⟨blk e i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hflt : ∀ i j, blk e i < blk e j → f i < f j := by
    intro i j h
    simp only [f, OrderIso.lt_iff_lt]
    exact h
  have hfinj : Function.Injective f := by
    intro i j h
    apply hinj
    have := (S.orderIsoOfFin hS).symm.injective h
    simpa using this
  let σ : Fin N ≃ Fin N := Equiv.ofBijective f ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  have hσ : ∀ i j, blk e i < blk e j → σ i < σ j := hflt
  have h1 : σ.toPEquiv.toMatrix * σ.symm.toPEquiv.toMatrix = (1 : Matrix (Fin N) (Fin N) k) := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  have h2 : σ.symm.toPEquiv.toMatrix * σ.toPEquiv.toMatrix = (1 : Matrix (Fin N) (Fin N) k) := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  let hh : GL (Fin N) k := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, h1, h2⟩
  have hent : ∀ (g : GL (Fin N) k) (i j : Fin N),
      ((hh * g * hh⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = (g : Matrix (Fin N) (Fin N) k) (σ i) (σ j) := by
    intro g i j
    have hv : ((hh * g * hh⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        = σ.toPEquiv.toMatrix * (g : Matrix (Fin N) (Fin N) k) * σ.symm.toPEquiv.toMatrix := rfl
    rw [hv, PEquiv.mul_toMatrix_apply, ← Equiv.toPEquiv_symm, Equiv.symm_symm, Equiv.toPEquiv_apply]
    simp only [Matrix.mul_assoc]
    rw [PEquiv.toMatrix_mul_apply, Equiv.toPEquiv_apply]
  have memR : ∀ n : unipB k (Fin N), hh * (n : GL (Fin N) k) * hh⁻¹ ∈ unipRad k e := by
    intro n
    have hn := (mem_unipB k).mp n.2
    rw [mem_unipRad, mem_parab]
    refine ⟨?_, ?_⟩
    · intro i j hij
      rw [hent]
      exact hn.1 _ _ (hσ _ _ hij)
    · intro a x y
      have hxy : x = y := by
        have h1 := x.isLt
        have h2 := y.isLt
        have h3 := hd a
        ext
        omega
      subst hxy
      rw [hent, hn.2, Matrix.one_apply_eq]
  rw [← not_subsingleton_iff_nontrivial] at hR ⊢
  intro hB
  apply hR
  change Subsingleton (V ⧸ GlobalTheory.PRep.twKer π _ 1) at hB
  change Subsingleton (V ⧸ GlobalTheory.PRep.twKer π _ 1)
  rw [Submodule.Quotient.subsingleton_iff] at hB ⊢
  have key : GlobalTheory.PRep.twKer π (unipB k (Fin N)) 1 ≤
      (GlobalTheory.PRep.twKer π (unipRad k e) 1).comap (π hh) := by
    unfold GlobalTheory.PRep.twKer
    rw [Submodule.span_le]
    rintro w ⟨n, v, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    apply Submodule.subset_span
    refine ⟨⟨hh * (n : GL (Fin N) k) * hh⁻¹, memR n⟩, π hh v, ?_⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (π hh⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [eq_top_iff]
  intro v _
  have hv : v = π hh (π hh⁻¹ v) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hv]
  exact key (hB ▸ Submodule.mem_top)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SlSpPreservesGrowthAndLevel
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.slSp_preserves_growth_and_level :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S : Submodule ℂ (archSmooth K n)), (Growth S → Growth (slSp e Γ S)) ∧ (Level S → Level (slSp e Γ S)) := by
  intro K _ _ a n e Γ S
  constructor
  · intro hG φ hφ
    induction hφ using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨ψ, hψ, g, -, hfm⟩ := hf
      obtain ⟨C, N, hC⟩ := hG ψ hψ
      have hC0 : 0 ≤ C := by
        have h1 := (norm_nonneg _).trans (hC 1)
        have hp : 0 < height (1 : AdelicGLn.AdelicGL K n) ^ N := pow_pos (height_pos _) N
        exact le_of_mul_le_mul_right (by rw [zero_mul]; exact h1) hp
      have hc : 0 ≤ heightConst K n * height g :=
        mul_nonneg (zero_le_one.trans (one_le_heightConst (K := K) (n := n))) (height_pos g).le
      refine ⟨C * (heightConst K n * height g) ^ N, N, fun m => ?_⟩
      have hh : height (g * emb e m) ≤ heightConst K n * height g * height m :=
        (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (UpperTheory.height_blockEmbedding_le K a n e m) hc)
      calc ‖(f : AdelicGLn.AdelicGL K a → ℂ) m‖ = ‖(ψ : AdelicGLn.AdelicGL K n → ℂ) (g * emb e m)‖ := by rw [hfm]
        _ ≤ C * height (g * emb e m) ^ N := hC _
        _ ≤ C * (heightConst K n * height g * height m) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le hh N) hC0
        _ = C * (heightConst K n * height g) ^ N * height m ^ N := by rw [mul_pow]; ring
    | zero => simpa using (hasModerateGrowth_zero (K := K) (n := a))
    | add x y _ _ hx hy => simpa using hx.add hy
    | smul c x _ hx => simpa using hx.smul c
  · rintro ⟨L, hL, hinv⟩
    let f : AdelicGLn.FiniteAdelicGL K a →* AdelicGLn.FiniteAdelicGL K n := emb e
    refine ⟨L.comap f, hL.preimage (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).2.2, fun φ hφ => ?_⟩
    induction hφ using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨ψ, hψ, g, -, hfm⟩ := hh
      intro u hu m
      rw [hfm, hfm, map_mul, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).1 u, ← mul_assoc]
      exact hinv ψ hψ (f u) hu _
    | zero => intro u _ m; simp
    | add x y _ _ hx hy => intro u hu m; simp [hx u hu m, hy u hu m]
    | smul c x _ hx => intro u hu m; simp [hx u hu m]
end

