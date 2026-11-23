module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OneLevelO
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem natL (ZL B' M V U J A S' PV PU PJ K a b c1 c2 e f Sel B ci : ℕ) (hB : 0 < B') (hM : 0 < M)
    (h1 : ZL * B' * M ^ (V + (U + J)) * A ≤ M * S' * (PV * (PU * PJ))) (h2 : S' ≤ B' * K ^ c2)
    (h3 : PV * K ^ a ≤ M ^ V * K ^ e) (h4 : PU ≤ M ^ U) (h5 : PJ ≤ M ^ J * K ^ f) (h6 : K ^ b ≤ A)
    (h7 : Sel * B ≤ ZL) (h8 : B * ci = M) (h9 : ci ≤ K ^ c1) :
    Sel * K ^ (a + b) ≤ K ^ (c1 + c2 + e + f) := by
  have k1 : ZL * K ^ (a + b) * (B' * M ^ (V + (U + J))) ≤ M * K ^ (c2 + e + f) * (B' * M ^ (V + (U + J))) := by
    calc ZL * K ^ (a + b) * (B' * M ^ (V + (U + J))) = ZL * B' * M ^ (V + (U + J)) * K ^ b * K ^ a := by ring
      _ ≤ ZL * B' * M ^ (V + (U + J)) * A * K ^ a := by gcongr
      _ ≤ M * S' * (PV * (PU * PJ)) * K ^ a := by gcongr
      _ = M * S' * (PV * K ^ a) * PU * PJ := by ring
      _ ≤ M * (B' * K ^ c2) * (M ^ V * K ^ e) * M ^ U * (M ^ J * K ^ f) := by gcongr
      _ = M * K ^ (c2 + e + f) * (B' * M ^ (V + (U + J))) := by ring
  have k2 : ZL * K ^ (a + b) ≤ M * K ^ (c2 + e + f) := Nat.le_of_mul_le_mul_right k1 (by positivity)
  have hB0 : 0 < B := Nat.pos_of_mul_pos_right (h8 ▸ hM : 0 < B * ci)
  refine Nat.le_of_mul_le_mul_right (c := B) ?_ hB0
  calc Sel * K ^ (a + b) * B = Sel * B * K ^ (a + b) := by ring
    _ ≤ ZL * K ^ (a + b) := by gcongr
    _ ≤ B * ci * K ^ (c2 + e + f) := by rw [h8]; exact k2
    _ ≤ B * K ^ c1 * K ^ (c2 + e + f) := by gcongr
    _ = K ^ (c1 + c2 + e + f) * B := by ring

private theorem block_le₂ {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (h : LC ρ) : (Bl ρ).toAddSubgroup ≤ (Zl ρ).toAddSubgroup := by
  intro z hz
  obtain ⟨m, hm⟩ := (mem_Bl ρ).1 hz
  have : z = fun g => ρ g m - m := funext hm
  subst this
  refine (mem_Zl ρ).2 ⟨(h m).comp (fun y => y - m), fun g g' => ?_⟩
  simp only [map_mul, Module.End.mul_apply, map_sub]
  abel

private theorem lc_comp {R Γ D M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group D] [TopologicalSpace D]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (h : LC ρ) (φ : D →* Γ) (hφ : Continuous φ) :
    LC (ρ.comp φ : Representation R D M) := fun m => (h m).comp_continuous hφ

private theorem zl_comp {R Γ D M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group D] [TopologicalSpace D]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (φ : D →* Γ) (hφ : Continuous φ) {z : Γ → M}
    (hz : z ∈ Zl ρ) : z ∘ φ ∈ Zl (ρ.comp φ : Representation R D M) :=
  ⟨hz.1.comp_continuous hφ, fun g g' => by simp [hz.2]⟩

theorem UpperTheory.V.Th.oneLevelO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (q d : ℕ) (a : ArData G q d) (rep rep' : Representation O G.Γ (Mm O n m)) (e : L.Vl → ℕ) (f : Option (Fin q) → ℕ) (c₁ c₂ : ℕ), l ≠ 2 → Cnts a → IsAd0 h y m rep → IsAd1 h y m rep' → (∀ v, Finite (Zbor y m v) ∧ Nat.card (Zbor y m v) ≤ Nat.card (ResidueField O) ^ e v) → (∀ j, Nat.card (Representation.invariants (rep'.comp (a.ι (.inr (.inr j))) : Representation O (a.D (.inr (.inr j))) _)) ≤ Nat.card (ResidueField O) ^ f j) → Nat.card rep.invariants ≤ Nat.card (ResidueField O) ^ c₁ → (Finite (Zl rep') → {z | z ∈ Zl rep' ∧ ∀ j : Fin q, z ∘ a.ι (.inr (.inr (some j))) ∈ Bl (rep'.comp (a.ι (.inr (.inr (some j)))) : Representation O (a.D (.inr (.inr (some j)))) _)}.ncard ≤ Nat.card (Bl rep') * Nat.card (ResidueField O) ^ c₂) → (trFun h y m '' Sel h y m).Finite ∧ (trFun h y m '' Sel h y m).ncard * Nat.card (ResidueField O) ^ (m * (n + n.choose 2) * Fintype.card L.Vl + m * n.choose 2 * d) ≤ Nat.card (ResidueField O) ^ (c₁ + c₂ + ∑ v, e v + ∑ j, f j) := by
  intro l _ L G G0 h O _ _ _ _ _ n y m q d a rep rep' e f c₁ c₂ hl hC hrep hrep' hZb hf hc1 hc2
  classical
  obtain ⟨h2, hOm⟩ := omFacts l O
  obtain ⟨hfD, -, hlD, -⟩ := hOm m
  haveI := hfD
  haveI : Finite (Mm O n m) := inferInstanceAs (Finite (Fin n → Fin n → Om O m))
  obtain ⟨k, b, hk, hb⟩ := pairP l L G G0 h O n y m a.c_ε
  have hb := hb rep rep' hrep hrep'
  have hLC : LC rep := (adExP l L G G0 h O n y m).2.2 rep (Or.inl hrep)
  have hι : ∀ w, Continuous (a.ι w) := by
    rintro (v | u | j)
    · exact continuous_subtype_val.comp (G.φ_cont v)
    · exact continuous_subtype_val.comp (G.φu_cont u)
    · exact continuous_subtype_val.comp (a.φq_cont j)
  have hLCw : ∀ w, LC (rep.comp (a.ι w) : Representation O (a.D w) _) := fun w => lc_comp rep hLC _ (hι w)
  have hpu : ∀ u g, h.p₀ (G.φu u g) = G0.φu u g := fun u g => Subtype.ext (h.φu u g)
  have hρ : ∀ u, ∀ g ∈ L.Ju u, y.ρm h m (G.φu u g) = 1 := fun u g hg => by
    have h1 : y.ρ (G0.φu u g) = 1 := y.ine u _ ⟨g, hg, rfl⟩
    have h3 : mat y.ρ (G0.φu u g) = 1 := congrArg Units.val h1
    rw [Pt.ρm, hpu, h3, red]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hu : ∀ u, ∀ g ∈ L.Ju u, rep (G.φu u g : G.Γ) = 1 := fun u g hg => by
    refine LinearMap.ext fun Z => ?_
    have := hrep.1 (G.φu u g) Z
    have e1 := hρ u g⁻¹ (inv_mem hg)
    rw [map_inv] at e1
    rw [hρ u g hg, one_smul, one_mul] at this
    exact this.trans ((congrArg (Z * ·) e1).trans (mul_one Z))
  let 𝓛 : ∀ w, AddSubgroup (a.D w → Mm O n m) := fun w => match w with
    | .inl v => (Bl (rep.comp (a.ι (.inl v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v
    | .inr (.inl u) => (Zl (rep.comp (a.ι (.inr (.inl u))) : Representation O (L.Gu u) _)).toAddSubgroup ⊓
        AddSubgroup.pi (L.Ju u : Set (L.Gu u)) (fun _ => ⊥)
    | .inr (.inr j) => (Zl (rep.comp (a.ι (.inr (.inr j))) : Representation O (a.Dq j) _)).toAddSubgroup
  have hloc := fun v => locSup l L G G0 h O n y m rep v hrep hLC (hZb v).1
  have h𝓛 : ∀ w, (Bl (rep.comp (a.ι w) : Representation O (a.D w) _)).toAddSubgroup ≤ 𝓛 w ∧
      𝓛 w ≤ (Zl (rep.comp (a.ι w) : Representation O (a.D w) _)).toAddSubgroup := by
    rintro (v | u | j)
    · exact ⟨le_sup_left, (hloc v).1⟩
    · refine ⟨le_inf (block_le₂ _ (hLCw _)) fun z hz g hg => ?_, inf_le_left⟩
      obtain ⟨Y, hy⟩ := (mem_Bl _).1 hz
      have e1 : rep (G.φu u g : G.Γ) Y - Y = 0 := by rw [hu u g hg]; simp
      exact AddSubgroup.mem_bot.2 ((hy g).trans e1)
    · exact ⟨block_le₂ _ (hLCw _), le_rfl⟩
  obtain ⟨hF, hF', hgw⟩ := hC.gw k hk O _ _ rep rep' b hLC hb 𝓛 h𝓛
  obtain ⟨hS1, hS2⟩ := selTr l L G G0 h O n y m rep hrep hLC hF
  have hS3 := (cCount O G.Γ (Mm O n m) rep G.c G.c_sq (h2 hl)).2.1
  refine ⟨hS1, ?_⟩
  have hFs : (Zl rep : Set (G.Γ → Mm O n m)).Finite := Set.toFinite _
  have hFs' : (Zl rep' : Set (G.Γ → Mm O n m)).Finite := Set.toFinite _
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.card_sum, Fintype.card_sum] at hgw
  haveI : Finite (Bl rep') := Finite.of_surjective _ (LinearMap.surjective_rangeRestrict _)
  refine natL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Nat.card_pos Nat.card_pos hgw ?_ ?_ ?_ ?_ ?_
    (hS2.trans ?_) hS3 hc1
  · refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (hc2 hF')
    exact fun y hy => ⟨hy.1, fun j => hy.2 _ rfl⟩
  · rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib,
      ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun v _ => ?_
    exact le_trans (hloc v).2.2 (Nat.mul_le_mul_left _ (hZb v).2)
  · rw [← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod' fun u _ => ?_
    have := (hC.unr u m O _ (rep.comp (a.ι (.inr (.inl u)))) (hLCw _) (fun Y => Matrix.ext fun i j => hlD (Y i j)) (hu u)).2
    rw [← Nat.card_coe_set_eq] at this
    exact this
  · rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun j _ => ?_
    have := (hC.locQ j k hk O _ _ (rep.comp (a.ι (.inr (.inr j)))) (rep'.comp (a.ι (.inr (.inr j)))) b (hLCw _)
      ⟨hb.left, hb.right, fun g y z => hb.equiv _ y z⟩).2
    rw [add_zero, pow_one] at this
    exact this.le.trans (Nat.mul_le_mul_left _ (hf j))
  · rw [pow_mul]
    conv_lhs => rw [← Fintype.card_fin d, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun i _ =>
      pow_choose_two_le_card_fixed_ad0_of_odd_involution l L G G0 h O n y m rep _ hl hrep (a.cw_sq i) (a.cw_η i)
  · refine Set.ncard_le_ncard ?_ (hFs.subset fun y hy => hy.1)
    rintro z ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    rintro (v | u | j)
    · exact h2 v
    · exact ⟨zl_comp rep _ (hι _) h1, fun g hg => h3 u g hg⟩
    · exact zl_comp rep _ (hι _) h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PsiCont
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem card_lt' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n.choose 2 := by
  rw [Fintype.card_subtype]
  have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))
  simpa using this

private theorem card_le' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 ≤ p.2} = n + n.choose 2 := by
  rw [← card_lt' n]
  have e : {p : Fin n × Fin n // p.1 ≤ p.2} ≃ Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2} :=
    { toFun := fun p => if h : p.1.1 < p.1.2 then .inr ⟨p.1, h⟩ else .inl p.1.1
      invFun := Sum.elim (fun i => ⟨(i, i), le_rfl⟩) fun p => ⟨p.1, p.2.le⟩
      left_inv := fun p => by
        by_cases h : p.1.1 < p.1.2
        · simp [h]
        · simp only [h, dite_false, Sum.elim_inl]
          exact Subtype.ext (Prod.ext rfl (le_antisymm p.2 (not_lt.1 h)))
      right_inv := by
        rintro (i | p)
        · simp
        · simp [p.2] }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin]

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) : red m (1 : Matrix (Fin n) (Fin n) O) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
private theorem filt_ht {Z Y ι : Type} [AddCommGroup Z] [AddCommGroup Y] [Fintype ι] (ht : ι → ℕ) (f : ι → Z →+ Y)
    (P : ι → Set Y) (h0 : ∀ z, (∀ i, f i z = 0) → z = 0) (hP : ∀ i, (P i).Finite)
    (hf : ∀ i z, (∀ j, ht j < ht i → f j z = 0) → f i z ∈ P i) : Finite Z ∧ Nat.card Z ≤ ∏ i, (P i).ncard := by
  let e₀ := (Fintype.equivFin ι).symm
  let e := (Tuple.sort (ht ∘ e₀)).trans e₀
  have hm : Monotone (ht ∘ e) := Tuple.monotone_sort (ht ∘ e₀)
  rw [← e.prod_comp]
  refine filtCount Z Y _ (fun i => f (e i)) (fun i => P (e i)) (fun z hz => h0 z fun i => ?_) (fun i => hP _)
    fun i z hz => hf _ z fun j hj => ?_
  · obtain ⟨i, rfl⟩ := e.surjective i
    exact hz i
  · obtain ⟨j, rfl⟩ := e.surjective j
    exact hz j (hm.reflect_lt hj)

private theorem conj_entry {R : Type} [CommRing R] {n : ℕ} (T B T' : Matrix (Fin n) (Fin n) R)
    (hT : ∀ i j, j < i → T i j = 0) (hT' : ∀ i j, j < i → T' i j = 0) (i j : Fin n)
    (hB : ∀ p q, i ≤ p → q ≤ j → (p ≠ i ∨ q ≠ j) → B p q = 0) : (T * B * T') i j = T i i * B i j * T' j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j, Matrix.mul_apply, Finset.sum_eq_single i]
  · intro p _ hp
    by_cases c : p < i
    · rw [hT i p c, zero_mul]
    · rw [hB p j (not_lt.1 c) le_rfl (.inl hp), mul_zero]
  · simp
  · intro q _ hq
    by_cases c : j < q
    · rw [hT' q j c, mul_zero]
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro p _
      by_cases c' : p < i
      · rw [hT i p c', zero_mul]
      · rw [hB p q (not_lt.1 c') (not_lt.1 c) (.inr hq), mul_zero]
  · simp

private theorem adic_mul {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f f' : D → R}
    (h : AdicCont I f) (h' : AdicCont I f') : AdicCont I fun g => f g * f' g := fun N => by
  simp only [map_mul]
  exact (h N).mul (h' N)

private theorem adic_sum {D R ι : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} (s : Finset ι) {f : ι → D → R}
    (h : ∀ i, AdicCont I (f i)) : AdicCont I fun g => ∑ i ∈ s, f i g := fun N => by
  classical
  induction s using Finset.induction_on with
  | empty => exact IsLocallyConstant.of_constant _ fun _ _ => rfl
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, map_add (f := _)]
    exact (h i N).add ih

section

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  (y : Pt G0.frame O n) (v : L.Vl)

private theorem psi_cont (i : Fin n) : AdicCont (maximalIdeal O) fun g : L.Gv v => (y.ψ v i g : O) := by
  have e : (fun g : L.Gv v => (y.ψ v i g : O)) = fun g => ∑ q, (∑ p, (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) i p *
      mat y.ρ (G0.φ v g) p q) * (y.w v : Matrix (Fin n) (Fin n) O) q i := funext fun g => ((y.tri v g).2 i).symm
  rw [e]
  exact adic_sum _ fun q => adic_mul (adic_sum _ fun p => adic_mul (fun N => IsLocallyConstant.const _)
    fun N => (y.cont p q N).comp_continuous (G0.φ_cont v)) fun N => IsLocallyConstant.const _

private noncomputable def cj (m : ℕ) (Z : Mm O n m) : Mm O n m :=
  red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * Z * red m (y.w v : Matrix (Fin n) (Fin n) O)

private theorem i2 (m : ℕ) :
    red m (y.w v : Matrix (Fin n) (Fin n) O) * red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
  rw [← red_mul, Units.mul_inv, red_one]

private theorem cj_rho (m : ℕ) (g : L.Gv v) : (∀ i j, j < i → cj y v m (y.ρ0 m (G0.φ v g)) i j = 0) ∧
    ∀ i, cj y v m (y.ρ0 m (G0.φ v g)) i i = algebraMap O (Om O m) (y.ψ v i g : O) := by
  have e : cj y v m (y.ρ0 m (G0.φ v g)) =
      red m (((y.w v)⁻¹ * y.ρ (G0.φ v g) * y.w v : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
    rw [Units.val_mul, Units.val_mul, red_mul, red_mul]; rfl
  rw [e]
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · exact (congrArg (Ideal.Quotient.mk _) ((y.tri v g).1 i j h)).trans (map_zero _)
  · exact congrArg (Ideal.Quotient.mk _) ((y.tri v g).2 i)

private noncomputable def crd (m : ℕ) (i j : Fin n) : Zbor y m v →+ (L.Gv v → Om O m) :=
  AddMonoidHom.mk' (fun β g => cj y v m (β.1 g) i j) fun β β' => funext fun g => by
    simp only [cj, AddSubgroup.coe_add, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]

private theorem crd_coc (m : ℕ) (i j : Fin n) (β : Zbor y m v)
    (hB : ∀ g p q, i ≤ p → q ≤ j → (p ≠ i ∨ q ≠ j) → cj y v m (β.1 g) p q = 0) :
    IsLocallyConstant (crd y v m i j β) ∧ ∀ g h, crd y v m i j β (g * h) =
      crd y v m i j β g + ((y.ψ v i g : O) * (y.ψ v j g⁻¹ : O)) • crd y v m i j β h := by
  refine ⟨β.2.1.comp fun Z : Mm O n m => cj y v m Z i j, fun g h => ?_⟩
  have e : cj y v m (β.1 (g * h)) = cj y v m (β.1 g) +
      cj y v m (y.ρ0 m (G0.φ v g)) * cj y v m (β.1 h) * cj y v m (y.ρ0 m (G0.φ v g⁻¹)) := by
    have i3 : ∀ M : Mm O n m, red m (y.w v : Matrix (Fin n) (Fin n) O) *
        (red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * M) = M := fun M => by
      rw [← mul_assoc, i2, one_mul]
    rw [β.2.2.1 g h, map_inv]
    simp only [cj, mul_add, add_mul, mul_assoc, i3]
  change cj y v m (β.1 (g * h)) i j = cj y v m (β.1 g) i j + _ • cj y v m (β.1 h) i j
  rw [e, Matrix.add_apply, conj_entry _ _ _ (cj_rho y v m g).1 (cj_rho y v m g⁻¹).1 i j (hB h), (cj_rho y v m g).2,
    (cj_rho y v m g⁻¹).2, Algebra.smul_def, map_mul]
  ring

end

theorem UpperTheory.V.Th.locVO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (v : L.Vl) (d : ℕ), LocCnt (L.Gv v) (G0.ε.comp (G0.η.ker.subtype.comp (G0.φ v))) d → (∃ g, algebraMap ℤ_[l] O (G0.ε (G0.φ v g) : ℤ_[l]) ≠ 1) → ∃ C : ℕ, ∀ m, Finite (Zbor y m v) ∧ Nat.card (Zbor y m v) ≤ Nat.card (ResidueField O) ^ (m * ((n + n.choose 2) * (1 + d)) + C) := by
  intro l _ L G0 O _ _ _ _ _ n y v d hL hε
  let P : ∀ m, {p : Fin n × Fin n // p.1 ≤ p.2} → Set (L.Gv v → Om O m) := fun m t =>
    {z | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ((y.ψ v t.1.1 g : O) * (y.ψ v t.1.2 g⁻¹ : O)) • z h}
  have hP : ∀ t, ∃ C : ℕ, ∀ m, (P m t).Finite ∧ (P m t).ncard ≤ Nat.card (ResidueField O) ^ (m * (1 + d) + C) := by
    rintro ⟨⟨i, j⟩, hij⟩
    let χ : L.Gv v →* Oˣ := y.ψ v i * (y.ψ v j)⁻¹
    have e : ∀ g, ((χ g : Oˣ) : O) = (y.ψ v i g : O) * (y.ψ v j g⁻¹ : O) := fun g => by
      show ((y.ψ v i g * (y.ψ v j g)⁻¹ : Oˣ) : O) = _
      rw [map_inv, Units.val_mul]
    have h := oneCntO l O (L.Gv v) _ d χ hL ?_ ?_
    · simpa only [e] using h
    · simp only [e]
      exact adic_mul (psi_cont y v i) fun N => (psi_cont y v j N).comp_continuous continuous_inv
    · rcases hij.lt_or_eq with hlt | heq
      · by_contra c
        push Not at c
        refine y.N1 v i j hlt (MonoidHom.ext fun g => ?_)
        have c' : y.ψ v i g * (y.ψ v j g)⁻¹ = G0.frame.eps O O (G0.φ v g) := Units.ext (c g)
        show y.ψ v i g = y.ψ v j g * G0.frame.eps O O (G0.φ v g)
        rw [← c', mul_comm, inv_mul_cancel_right]
      · obtain ⟨g, hg⟩ := hε
        refine ⟨g, fun c => hg ?_⟩
        have hij' : i = j := heq
        subst hij'
        have c1 : χ g = 1 := mul_inv_cancel (y.ψ v i g)
        rw [c1] at c
        exact c.symm
  choose C hC using hP
  refine ⟨∑ t, C t, fun m => ?_⟩
  refine And.imp_right (fun h2 => ?_) <| filt_ht (fun t : {p : Fin n × Fin n // p.1 ≤ p.2} => (t.1.2 : ℕ) - t.1.1)
    (fun t => crd y v m t.1.1 t.1.2) (P m) (fun β h => ?_) (fun t => (hC t m).1) fun t β h => ?_
  · refine h2.trans ((Finset.prod_le_prod' fun t _ => (hC t m).2).trans (le_of_eq ?_))
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_le', smul_eq_mul]
    congr 1
    ring
  · refine Subtype.ext (funext fun g => ?_)
    have e0 : cj y v m (β.1 g) = 0 := Matrix.ext fun p q => by
      by_cases c : q < p
      · exact β.2.2.2 g p q c
      · exact congrFun (h ⟨(p, q), not_lt.1 c⟩) g
    have e1 := congrArg (fun M => red m (y.w v : Matrix (Fin n) (Fin n) O) * M *
      red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) e0
    simp only [cj, ← mul_assoc, i2, one_mul, mul_zero, zero_mul] at e1
    rwa [mul_assoc, i2, mul_one] at e1
  · exact crd_coc y v m t.1.1 t.1.2 β fun g p q c1 c2 c3 => by
      by_cases c : q < p
      · exact β.2.2.2 g p q c
      · refine congrFun (h ⟨(p, q), not_lt.1 c⟩ ?_) g
        simp only [Fin.le_def, Fin.lt_def, ne_eq, Fin.ext_iff] at c c1 c2 c3 ⊢
        omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.TwistedCocycleApplyOne
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

section Abs

variable {K R M : Type} [Group K] [CommRing R] [Ring M] [Module R M] (ρ z : K → M) (χ : K → R)
  (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h) (c1 : χ 1 = 1) (cm : ∀ g h, χ (g * h) = χ g * χ h)
  (hz : ∀ g h, z (g * h) = z g + χ g • (ρ g * z h * ρ g⁻¹))

include h1 c1 hz in
private theorem twisted_cocycle_apply_one : z 1 = 0 := by
  have := hz 1 1
  rw [mul_one, inv_one, h1, c1, one_mul, mul_one, one_smul] at this
  exact left_eq_add.1 this

private theorem tw_inv {N : Type} [Monoid N] (ρ : K → N) (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h)
    {g : K} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := hm g g⁻¹
  rw [mul_inv_cancel, h1, hg, one_mul] at this
  exact this.symm

include h1 hm hz in
private theorem tw_add {g : K} (hg : ρ g = 1) (hc : χ g = 1) (h : K) : z (g * h) = z g + z h := by
  rw [hz, tw_inv ρ h1 hm hg, hg, hc, one_mul, mul_one, one_smul]

include h1 hm c1 cm hz in
private theorem tw_U [TopologicalSpace K] (cρ : IsLocallyConstant ρ) (cχ : IsLocallyConstant χ)
    (cz : IsLocallyConstant z) :
    ∃ U : OpenNormalSubgroup K, ∀ g, g ∈ U ↔ ρ g = 1 ∧ χ g = 1 ∧ z g = 0 := by
  let S : Subgroup K :=
    { carrier := {g | ρ g = 1 ∧ χ g = 1 ∧ z g = 0}
      one_mem' := ⟨h1, c1, twisted_cocycle_apply_one ρ z χ h1 c1 hz⟩
      mul_mem' := fun {a b} ha hb => ⟨by rw [hm, ha.1, hb.1, one_mul], by rw [cm, ha.2.1, hb.2.1, one_mul],
        by rw [tw_add ρ z χ h1 hm hz ha.1 ha.2.1, ha.2.2, hb.2.2, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨tw_inv ρ h1 hm ha.1, tw_inv χ c1 cm ha.2.1, by
        have := tw_add ρ z χ h1 hm hz ha.1 ha.2.1 a⁻¹
        rw [mul_inv_cancel, twisted_cocycle_apply_one ρ z χ h1 c1 hz, ha.2.2, zero_add] at this
        exact this.symm⟩ }
  have hN : S.Normal := ⟨fun u hu g => ⟨by
      rw [hm, hm, hu.1, mul_one, ← hm, mul_inv_cancel, h1], by
      rw [cm, cm, hu.2.1, mul_one, ← cm, mul_inv_cancel, c1], by
      rw [mul_assoc, hz, tw_add ρ z χ h1 hm hz hu.1 hu.2.1, hu.2.2, zero_add, ← hz, mul_inv_cancel,
        twisted_cocycle_apply_one ρ z χ h1 c1 hz]⟩⟩
  have hO : IsOpen (S : Set K) := (cρ {1}).inter ((cχ {1}).inter (cz {0}))
  exact ⟨⟨⟨S, hO⟩, hN⟩, fun g => Iff.rfl⟩

end Abs

private theorem tw_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have : ∀ᶠ g in nhds g0, ∀ i j, f g i j = f g0 i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g0
  filter_upwards [this] with g hg
  exact Matrix.ext hg

private theorem tw_core {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hK
  haveI : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : IsClosed (K.normalCore : Set Γ) := Subgroup.normalCore_isClosed K (K.isClosed_of_isOpen hK)
  have ho : IsOpen (K.normalCore : Set Γ) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hc
  exact ⟨{ toSubgroup := K.normalCore, isOpen' := ho, isNormal' := inferInstance },
    Subgroup.normal_le_normalCore.2 hP, K.normalCore_le⟩

private theorem phEq_one (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n)
    (m : ℕ) (hPL : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1)
    (z : G0.G₀ → Mm O n m) (cz : IsLocallyConstant z)
    (hz : ∀ g h : G0.G₀, z (g * h) = z g + epsm O G0 m g • (y.ρ0 m g * z h * y.ρ0 m g⁻¹))
    (j : Fin T.q) : ∀ᶠ N in atTop, y.ρ0 m ((T.h N).p₀ (T.ph N j)) = y.ρ0 m (T.sg j) ∧
      epsm O G0 m ((T.h N).p (T.ph N j)) = 1 ∧ z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
  obtain ⟨-, -, -, f4, f5⟩ := (omFacts l O).2 m
  have r1 : y.ρ0 m 1 = 1 := by
    show (Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix (mat y.ρ 1) = 1
    rw [map_one, map_one]
  have r2 : ∀ g h, y.ρ0 m (g * h) = y.ρ0 m g * y.ρ0 m h := fun g h => by
    show (Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix (mat y.ρ (g * h)) = _
    rw [map_mul, map_mul]
    rfl
  have c1 : IsLocallyConstant fun g : G0.G₀ => y.ρ0 m g := tw_lc _ fun a b => y.cont a b m
  have e1 : epsm O G0 m ((1 : G0.G₀) : G0.Γ) = 1 := by simp [epsm]
  have em : ∀ g h : G0.G₀, epsm O G0 m ((g * h : G0.G₀) : G0.Γ) = epsm O G0 m g * epsm O G0 m h := by
    intro g h
    simp [epsm]
  have c2 : IsLocallyConstant fun g : G0.G₀ => epsm O G0 m g := by
    have hc : Continuous fun g : G0.G₀ => ((G0.ε g : ℤ_[l]ˣ) : ℤ_[l]) :=
      Units.continuous_val.comp (G0.ε_cont.comp continuous_subtype_val)
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have ho : IsOpen {a : ℤ_[l] | PadicInt.toZModPow m a = 1} := by
      have : {a : ℤ_[l] | PadicInt.toZModPow m a = 1} = Metric.closedBall 1 ((l : ℝ) ^ (-(m : ℤ))) := by
        ext a
        rw [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
          ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      rw [this]
      exact IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
    have h1 := (ho.preimage (hc.comp (continuous_mul_const g0⁻¹))).mem_nhds (x := g0) (by
      show PadicInt.toZModPow m ((G0.ε ((g0 * g0⁻¹ : G0.G₀) : G0.Γ) : ℤ_[l]ˣ) : ℤ_[l]) = 1
      rw [mul_inv_cancel, OneMemClass.coe_one, map_one, Units.val_one, map_one])
    filter_upwards [h1] with g hg
    have h2 : epsm O G0 m ((g * g0⁻¹ : G0.G₀) : G0.Γ) = 1 := f4 _ hg
    have h3 := em (g * g0⁻¹) g0
    rw [inv_mul_cancel_right, h2, one_mul] at h3
    exact h3
  obtain ⟨U, hU⟩ := tw_U (K := G0.G₀) (fun g => y.ρ0 m g) z (fun g => epsm O G0 m g) r1 r2 e1 em hz c1 c2 cz
  haveI := T.H.isNormal'
  obtain ⟨hn, -, hle, -⟩ := pl_props l G0.Γ T.H.toSubgroup T.H.toOpenSubgroup.isOpen
  have hsub : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → g ∈ U := fun g hg => by
    obtain ⟨a1, a2, a3⟩ := plKill l L G0 T O n y m G0 (Glob.Hom.refl G0) hPL z cz hz g hg
    exact (hU g).2 ⟨a2, a3, a1⟩
  obtain ⟨V, v1, v2⟩ := tw_core (U.toSubgroup.map G0.η.ker.subtype) (PL l T.H.toSubgroup)
    (G0.η_open.isOpenMap_subtype_val _ U.toOpenSubgroup.isOpen)
    fun a ha => ⟨⟨a, T.H_η a (hle ha)⟩, hsub _ ha, rfl⟩
  filter_upwards [T.ph_lim V j v1] with N hN
  obtain ⟨u, hu, e⟩ := v2 hN
  obtain ⟨u1, u2, u3⟩ := (hU u).1 hu
  have e' : (T.h N).p₀ (T.ph N j) = u * T.sg j := Subtype.ext (eq_mul_inv_iff_mul_eq.1 e).symm
  have hs : epsm O G0 m (T.sg j : G0.Γ) = 1 := by
    have : G0.ε (T.sg j) = 1 := T.sg_mem j
    simp [epsm, this]
  refine ⟨?_, ?_, ?_⟩
  · rw [e']
    exact (r2 _ _).trans (by rw [u1, one_mul])
  · show epsm O G0 m (((T.h N).p₀ (T.ph N j) : G0.G₀) : G0.Γ) = 1
    rw [e', em, u2, hs, one_mul]
  · rw [e', tw_add (K := G0.G₀) (fun g => y.ρ0 m g) z (fun g => epsm O G0 m g) r1 r2 hz u1 u2, u3, zero_add]

theorem UpperTheory.V.Th.phEqO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ), PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → ∀ᶠ N in atTop, ∀ j, y.ρ0 m ((T.h N).p₀ (T.ph N j)) = y.ρ0 m (T.sg j) ∧ epsm O G0 m ((T.h N).p (T.ph N j)) = 1 ∧ ∀ z ∈ Tw y m, z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
  intro l _ L G0 T O _ _ _ _ _ n y m hΦ hPL
  refine Filter.eventually_all.2 fun j => ?_
  have h0 := phEq_one l L G0 T O n y m hPL 0 (IsLocallyConstant.const 0) (fun g h => by simp) j
  have h1 : ∀ᶠ N in atTop, ∀ z ∈ Tw y m, z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
    refine (Filter.eventually_all_finite (finTwO l L G0 O n y m hΦ)).2 fun z hz => ?_
    exact (phEq_one l L G0 T O n y m hPL z hz.1 hz.2.1 j).mono fun N h => h.2.2
  filter_upwards [h0, h1] with N a b
  exact ⟨a.1, a.2.1, b⟩
end

