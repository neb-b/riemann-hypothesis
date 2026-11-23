module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.MemW1IffPattern
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FixBdQZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.BdCard
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have : ∀ᶠ g in nhds g0, ∀ i j, f g i j = f g0 i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g0
  filter_upwards [this] with g hg
  exact Matrix.ext hg

private theorem block_le₂ {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (h : LC ρ) : Bl ρ ≤ Zl ρ := by
  intro z hz
  obtain ⟨m, hm⟩ := (mem_Bl ρ).1 hz
  obtain rfl : z = fun g => ρ g m - m := funext hm
  refine ⟨(h m).comp (· - m), fun g h => ?_⟩
  simp only [map_mul, map_sub, Module.End.mul_apply]
  abel

private theorem bd_card {l : ℕ} [Fact l.Prime] (F : GFrame l) {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
    {n : ℕ} (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R))
    (rep : Representation A F.Γ V) (had : IsAd F ρ (fun _ => 1) V rep) (hlc : LC rep) :
    (Bd F ρ V).ncard = {z | z ∈ Bl rep ∧ z F.c = 0}.ncard := by
  have hP := (polZ l F A R n ρ _ V rep had).2
  obtain ⟨a1, a2⟩ := had
  simp only [one_smul] at a1 a2
  have e : Bd F ρ V = (fun (y : F.Γ → V) (g : F.G₀) => (y g : Matrix (Fin n) (Fin n) R)) ''
      {z | z ∈ Bl rep ∧ z F.c = 0} := by
    ext z
    constructor
    · rintro ⟨Y, hY, hT, rfl⟩
      refine ⟨fun g => rep g ⟨Y, hY⟩ - ⟨Y, hY⟩, ⟨(mem_Bl rep).2 ⟨_, fun _ => rfl⟩, ?_⟩, ?_⟩
      · refine sub_eq_zero.2 (Subtype.ext ?_)
        rw [a2]
        show -Yᵀ = Y
        rw [hT, neg_neg]
      · funext g
        show ((rep g ⟨Y, hY⟩ - ⟨Y, hY⟩ : V) : Matrix (Fin n) (Fin n) R) = _
        rw [Submodule.coe_sub, a1]
        rfl
    · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
      obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hy
      refine ⟨Y, Y.2, ?_, funext fun g => ?_⟩
      · rw [hY, sub_eq_zero] at hc
        have := a2 Y
        rw [hc] at this
        exact neg_eq_iff_eq_neg.1 this.symm
      · show (y g : Matrix (Fin n) (Fin n) R) = _
        rw [hY, Submodule.coe_sub, a1]
        rfl
  rw [e, Set.InjOn.ncard_image]
  rintro y ⟨h1, h2⟩ y' ⟨h3, h4⟩ hh
  refine sub_eq_zero.1 ((hP (y - y') (block_le₂ rep hlc (sub_mem h1 h3)) ?_).2 fun g => ?_)
  · rw [Pi.sub_apply, h2, h4, sub_zero]
  · exact sub_eq_zero.2 (Subtype.ext (congrFun hh g))

theorem UpperTheory.V.Pa.selN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ) (rep : Representation x.A G.Γ (k.M1 (x.Am m))), l ≠ 2 → IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) (fun _ => 1) (k.M1 (x.Am m)) rep → Finite (Zl rep) → (Sel1 h (x.Am m) k).Finite ∧ (Sel1 h (x.Am m) k).ncard * Nat.card (k.M1 (x.Am m)) ≤ {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation x.A (L.Gv v) _)).toAddSubgroup ⊔ k.Zb (x.Am m) v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}.ncard * Nat.card {y : k.M1 (x.Am m) // rep G.c y = y} ∧ (Bd1 h (x.Am m) k).ncard * Nat.card rep.invariants = Nat.card {y : k.M1 (x.Am m) // rep G.c y = y} := by
  intro l _ L G G0 h n x k m rep hl had hfin
  obtain ⟨-, -, fD, -, -, -, ht, h2, -⟩ := finAm l G0.frame n x m k.g
  have hlc : LC rep := (lc1 l L G G0 h n x k m).2.2 _ _ rep (IsLocallyConstant.const _) had
  obtain ⟨-, -, -, -, hine⟩ := rho1 l G0.frame n x k (x.Am m)
  haveI : Finite (k.M1 (x.Am m)) := Subtype.finite
  obtain ⟨c1, -, c3⟩ := cCount x.A G.Γ (k.M1 (x.Am m)) rep G.c G.c_sq (h2 hl)
  have hP := (polZ l G.frame x.A _ n _ _ _ rep had).1
  have a1 : ∀ (g : G.G₀) (Z : k.M1 (x.Am m)), (rep g Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) =
      k.ρ1 (x.Am m) (h.p₀ g) * Z * k.ρ1 (x.Am m) (h.p₀ g⁻¹) := fun g Z => (had.1 g Z).trans (one_smul _ _)
  have pφ : ∀ v g, h.p₀ (G.φ v g) = G0.φ v g := fun v g => Subtype.ext (h.φ v g)
  have pφu : ∀ u g, h.p₀ (G.φu u g) = G0.φu u g := fun u g => Subtype.ext (h.φu u g)
  let Z : AddSubgroup (G.Γ → k.M1 (x.Am m)) :=
    { carrier := {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation x.A (L.Gv v) _)).toAddSubgroup ⊔ k.Zb (x.Am m) v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}
      add_mem' := fun ⟨p1, p2, p3⟩ ⟨q1, q2, q3⟩ => ⟨add_mem p1 q1, fun v => add_mem (p2 v) (q2 v), fun u g hg => by
        rw [Pi.add_apply, p3 u g hg, q3 u g hg, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun v => zero_mem _, fun _ _ _ => rfl⟩
      neg_mem' := fun ⟨p1, p2, p3⟩ => ⟨neg_mem p1, fun v => neg_mem (p2 v), fun u g hg => by
        rw [Pi.neg_apply, p3 u g hg, neg_zero]⟩ }
  have fZ : (Z : Set (G.Γ → k.M1 (x.Am m))).Finite :=
    (Set.toFinite (Zl rep : Set (G.Γ → k.M1 (x.Am m)))).subset fun z hz => hz.1
  have hB : (Bl rep).toAddSubgroup ≤ Z := by
    intro z hz
    refine ⟨block_le₂ rep hlc hz, fun v => AddSubgroup.mem_sup_left ?_, fun u g hg => ?_⟩
    · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hz
      exact (mem_Bl _).2 ⟨Y, fun g => hY _⟩
    · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hz
      rw [hY, sub_eq_zero]
      refine Subtype.ext ?_
      rw [a1, ← map_inv, pφu, pφu, hine u _ ⟨g, hg, rfl⟩, hine u _ ⟨g⁻¹, inv_mem hg, rfl⟩, one_mul, mul_one]
  have hc := c1 Z fZ hB fun z hz => hz.1.2
  have fS : {z | z ∈ Z ∧ z G.c = 0}.Finite := fZ.subset fun z hz => hz.1
  have hsub : Sel1 h (x.Am m) k ⊆ (fun (y : G.Γ → k.M1 (x.Am m)) (g : G.G₀) =>
      (y g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))) '' {z | z ∈ Z ∧ z G.c = 0} := by
    rintro z ⟨s1, s2, s3, s4, s5, s6⟩
    obtain ⟨y, y1, y2, y3⟩ := hP z s1 (lc_mat z fun i j => (adicLC _ _ _ m _ ht).1 (s2 i j))
      (fun g g' => by rw [one_smul]; exact s3 g g') (fun g => by rw [one_smul]; exact s4 g)
    refine ⟨y, ⟨⟨y1, fun v => ?_, fun u g hg => Subtype.ext ?_⟩, y2⟩, funext y3⟩
    · obtain ⟨Y, hY, hloc⟩ := s6 v
      have hb : (fun g => rep g ⟨Y, hY⟩ - ⟨Y, hY⟩) ∈ Bl rep := (mem_Bl rep).2 ⟨_, fun _ => rfl⟩
      obtain ⟨w1, w2⟩ := sub_mem y1 (block_le₂ rep hlc hb)
      set β : G.Γ → k.M1 (x.Am m) := y - fun g => rep g ⟨Y, hY⟩ - ⟨Y, hY⟩ with hβ
      have hv : ∀ g : G.G₀, (β g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) =
          z g - dY G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) Y g := fun g => by
        rw [hβ, Pi.sub_apply, Submodule.coe_sub, Submodule.coe_sub, a1, y3]
        rfl
      refine AddSubgroup.mem_sup.2 ⟨fun g => rep (G.φ v g) ⟨Y, hY⟩ - ⟨Y, hY⟩, (mem_Bl _).2 ⟨_, fun _ => rfl⟩,
        fun g => β (G.φ v g), ⟨?_, fun g g' => ?_, fun g i j hij => ?_, fun g hg i => ?_⟩, ?_⟩
      · exact w1.comp_continuous (continuous_subtype_val.comp (G.φ_cont v))
      · show (β (G.φ v (g * g')) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) = β (G.φ v g) +
          k.ρ1 (x.Am m) (G0.φ v g) * β (G.φ v g') * k.ρ1 (x.Am m) (G0.φ v g)⁻¹
        rw [map_mul, Subgroup.coe_mul, w2, Submodule.coe_add, a1, map_inv, pφ]
      · show (k.wi1 (x.Am m) v * (β (G.φ v g) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * k.w1 (x.Am m) v) i j = 0
        rw [hv]
        exact (hloc g).1 i j hij
      · show (k.wi1 (x.Am m) v * (β (G.φ v g) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * k.w1 (x.Am m) v) i i = 0
        rw [hv]
        exact (hloc g).2 hg i
      · funext g
        exact add_sub_cancel _ _
    · exact (y3 _).trans (s5 u _ ⟨g, hg, rfl⟩)
  refine ⟨(fS.image _).subset hsub, ?_, ?_⟩
  · refine le_trans (Nat.mul_le_mul_right _ (((Set.ncard_le_ncard hsub (fS.image _))).trans (Set.ncard_image_le fS))) ?_
    exact hc.symm.le
  · exact (congrArg (· * _) (bd_card G.frame _ _ rep had hlc)).trans c3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.CardCnd
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {X : Type} [CommRing X] {g n : ℕ}

private def Cnd (lo same : Prop) (d : DD X g) : Prop :=
  (lo → d = 0) ∧ d.ep' = 0 ∧ d.eta = 0 ∧ (same → d.ep = 0) ∧ (¬ same → d.a = 0)

private theorem card_cnd (lo same : Prop) [Decidable lo] [Decidable same] :
    Nat.card {d : DD X g // Cnd lo same d} = Nat.card X ^ (if lo then 0 else if same then 1 else g) := by
  by_cases hlo : lo
  · rw [if_pos hlo, pow_zero, Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩, fun d => Subtype.ext (d.2.1 hlo)⟩
  · by_cases hs : same
    · rw [if_neg hlo, if_pos hs, pow_one]
      exact Nat.card_congr
        { toFun := fun d => d.1.a
          invFun := fun y => ⟨⟨y, 0, 0, 0⟩, fun h => absurd h hlo, rfl, rfl, fun _ => rfl, fun h => absurd hs h⟩
          left_inv := fun d => Subtype.ext (DD.ext rfl (d.2.2.2.2.1 hs).symm d.2.2.1.symm d.2.2.2.1.symm)
          right_inv := fun y => rfl }
    · rw [if_neg hlo, if_neg hs]
      have e : {d : DD X g // Cnd lo same d} ≃ (Fin g → X) :=
        { toFun := fun d => d.1.ep
          invFun := fun f => ⟨⟨0, f, 0, 0⟩, fun h => absurd h hlo, rfl, rfl, fun h => absurd h hs, fun _ => rfl⟩
          left_inv := fun d => Subtype.ext (DD.ext (d.2.2.2.2.2 hs).symm rfl d.2.2.1.symm d.2.2.2.1.symm)
          right_inv := fun f => rfl }
      rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin]

private theorem sum_exp (ty : Fin n → Bool) :
    (∑ p : Fin n × Fin n, if p.2 < p.1 then 0 else if ty p.1 = ty p.2 then 1 else g) =
      n + ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ ty p.1 = ty p.2).card +
        g * (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ ty p.1 ≠ ty p.2).card) := by
  have h : ∀ p : Fin n × Fin n, (if p.2 < p.1 then 0 else if ty p.1 = ty p.2 then 1 else g) =
      (if p.1 = p.2 then 1 else 0) + ((if p.1 < p.2 ∧ ty p.1 = ty p.2 then 1 else 0) +
        g * (if p.1 < p.2 ∧ ty p.1 ≠ ty p.2 then 1 else 0)) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with hp | hp | hp
    · have h1 : ¬ p.2 < p.1 := not_lt.2 hp.le
      have h2 : p.1 ≠ p.2 := hp.ne
      by_cases ht : ty p.1 = ty p.2 <;> simp [hp, h1, h2, ht]
    · simp [hp]
    · have h1 : ¬ p.1 < p.2 := not_lt.2 hp.le
      have h2 : p.1 ≠ p.2 := hp.ne'
      simp [hp, h1, h2]
  rw [Finset.sum_congr rfl fun p _ => h p, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, Nat.cast_id]
  congr 1
  have hd : (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2) = Finset.diag Finset.univ := by
    ext p
    simp [Finset.mem_diag]
  rw [hd, Finset.diag_card, Finset.card_univ, Fintype.card_fin]

private theorem card_pat (ty : Fin n → Bool) :
    Nat.card {Z : Matrix (Fin n) (Fin n) (DD X g) // ∀ i j, Cnd (j < i) (ty i = ty j) (Z i j)} =
      Nat.card X ^ (∑ p : Fin n × Fin n, if p.2 < p.1 then 0 else if ty p.1 = ty p.2 then 1 else g) := by
  have e : {Z : Matrix (Fin n) (Fin n) (DD X g) // ∀ i j, Cnd (j < i) (ty i = ty j) (Z i j)} ≃
      ((p : Fin n × Fin n) → {d : DD X g // Cnd (p.2 < p.1) (ty p.1 = ty p.2) d}) :=
    { toFun := fun Z p => ⟨Z.1 p.1 p.2, Z.2 _ _⟩
      invFun := fun f => ⟨fun i j => (f (i, j)).1, fun i j => (f (i, j)).2⟩
      left_inv := fun Z => Subtype.ext rfl
      right_inv := fun f => funext fun p => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun p _ => ?_
  exact card_cnd _ _

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.bCard :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (m : ℕ) (v : F.Vl), Nat.card (k.b1 (x.Am m) v) = Nat.card x.K ^ (m * (n + nu n x.a k.g)) := by
  intro l _ F n x k m v
  obtain ⟨_, hK, -⟩ := finAm l F n x m k.g
  obtain ⟨-, hnu, -⟩ := tyCard l F n x v k.g
  obtain ⟨hw, hw'⟩ := (rho1 l F n x k (x.Am m)).2.2.2.1 v
  have hM := (tri l F n x k (x.Am m) v).2
  have c1 : ∀ Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g),
      k.wi1 (x.Am m) v * (k.w1 (x.Am m) v * Y * k.wi1 (x.Am m) v) * k.w1 (x.Am m) v = Y := by
    intro Y
    simp only [Matrix.mul_assoc]
    rw [hw, Matrix.mul_one, ← Matrix.mul_assoc, hw, Matrix.one_mul]
  have c2 : ∀ Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g),
      k.w1 (x.Am m) v * (k.wi1 (x.Am m) v * Y * k.w1 (x.Am m) v) * k.wi1 (x.Am m) v = Y := by
    intro Y
    simp only [Matrix.mul_assoc]
    rw [hw', Matrix.mul_one, ← Matrix.mul_assoc, hw', Matrix.one_mul]
  have e : k.b1 (x.Am m) v ≃ {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) //
      ∀ i j, Cnd (j < i) (x.ty v i = x.ty v j) (Y i j)} :=
    { toFun := fun Z => ⟨k.wi1 (x.Am m) v * Z.1.1 * k.w1 (x.Am m) v, fun i j =>
        have hT := (hM Z.1.1).1 Z.1.2 i j
        ⟨Z.2 i j, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2⟩⟩
      invFun := fun Y => ⟨⟨k.w1 (x.Am m) v * Y.1 * k.wi1 (x.Am m) v, (hM _).2 (by
          rw [c1]
          intro i j
          have hc := Y.2 i j
          exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩)⟩, by
          intro i j hij
          show (k.wi1 (x.Am m) v * (k.w1 (x.Am m) v * Y.1 * k.wi1 (x.Am m) v) * k.w1 (x.Am m) v) i j = 0
          rw [c1]
          exact (Y.2 i j).1 hij⟩
      left_inv := fun Z => Subtype.ext (Subtype.ext (c2 _))
      right_inv := fun Y => Subtype.ext (c1 _) }
  rw [Nat.card_congr e, card_pat, sum_exp, hnu, hK, ← pow_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.CommutingMatrixOffdiagZero
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private def ddBaseRingHom (X : Type) [CommRing X] (g : ℕ) : DD X g →+* X where
  toFun := DD.a
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private def ddEpsCoordAddHom (X : Type) [CommRing X] (g : ℕ) (j : Fin g) : DD X g →+ X where
  toFun y := y.ep j
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem commuting_matrix_offdiag_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n)
    (Z : Matrix (Fin n) (Fin n) x.A) (hZ : ∀ g, mat x.ρ g * Z = Z * mat x.ρ g) (i j : Fin n) (hij : i ≠ j) :
    Z i j = 0 := by
  have hmem : Matrix.single j j (1 : x.A) ∈ Ev (PowerSeries x.K) (PowerSeries x.K) n x.a := by
    show ∀ i' j' : Fin n, _
    intro i' j'
    refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
    rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h Iff.rfl
  obtain ⟨s, hs⟩ := x.span _ hmem
  have hcomm : ∀ M ∈ Submodule.span (PowerSeries x.K) (⇑(mat x.ρ) '' ↑F.G'), Z * M = M * Z := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, -, rfl⟩ := hM
      exact (hZ g).symm
    | zero => simp
    | add M N _ _ hM hN => rw [Matrix.mul_add, Matrix.add_mul, hM, hN]
    | smul c M _ hM => rw [Matrix.mul_smul, Matrix.smul_mul, hM]
  have h1 := hcomm _ hs
  rw [Matrix.mul_smul, Matrix.smul_mul] at h1
  have h2 := congrFun (congrFun h1 i) j
  simpa [hij, PowerSeries.X_ne_zero] using h2

private theorem skew_commuting_matrix_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (hl : l ≠ 2)
    (Z : Matrix (Fin n) (Fin n) x.A) (hZ : ∀ g, mat x.ρ g * Z = Z * mat x.ρ g) (ht : Zᵀ = -Z) : Z = 0 := by
  have h2u : IsUnit (2 : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
    have h' : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
    have hl' : l ∣ 2 := by exact_mod_cast h'
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hl')
  have hu : IsUnit (2 : x.A) := by
    have := h2u.map ((algebraMap x.K (PowerSeries x.K)).comp (algebraMap ℤ_[l] x.K))
    rwa [map_ofNat] at this
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    have h1 := congrFun (congrFun ht i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
    have h2 : (2 : x.A) * Z i i = 0 := by linear_combination h1
    simpa using hu.mul_right_eq_zero.mp h2
  · exact commuting_matrix_offdiag_zero x Z hZ i j hij

private theorem rho1_map_ddBaseRingHom_eq_mat_rho {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (g : F.G₀) :
    (k.ρ1 x.A g).map (ddBaseRingHom x.A k.g) = mat x.ρ g := by
  have ha : ∀ y, ddBaseRingHom x.A k.g y = y.a := fun _ => rfl
  have hb : ∀ y : x.A, (algebraMap x.A (DD x.A k.g) y).a = y := fun _ => rfl
  have h0 : (0 : DD x.A k.g).a = 0 := rfl
  rw [Kap.ρ1, Matrix.map_mul]
  refine Matrix.ext fun i j => ?_
  simp [ha, hb, h0, DD.epM, NP.ρX, Matrix.mul_apply, Matrix.one_apply, apply_ite DD.a, DD.one_a]

private theorem map_ep_mul_eq_leibniz {X : Type} [CommRing X] {g n : ℕ} (M N : Matrix (Fin n) (Fin n) (DD X g)) (j : Fin g) :
    (M * N).map (fun y => y.ep j) = M.map DD.a * N.map (fun y => y.ep j) + M.map (fun y => y.ep j) * N.map DD.a := by
  refine Matrix.ext fun r c => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show (∑ t, M r t * N t c).ep j = ∑ t, (M r t * N t c).ep j from map_sum (ddEpsCoordAddHom X g j) _ _]
  simp [DD.mul_ep]

private theorem map_a_mul_eq_map_a_mul_map_a {X : Type} [CommRing X] {g n : ℕ} (M N : Matrix (Fin n) (Fin n) (DD X g)) :
    (M * N).map DD.a = M.map DD.a * N.map DD.a :=
  Matrix.map_mul (f := ddBaseRingHom X g)

private theorem skew_invariant_M1_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (hl : l ≠ 2)
    (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)) (hm : Z ∈ k.M1 x.A) (ht : Zᵀ = -Z)
    (hZ : ∀ g, k.ρ1 x.A g * Z * k.ρ1 x.A g⁻¹ = Z) : Z = 0 := by
  have hA0 : ∀ g : F.G₀, (k.ρ1 x.A g).map DD.a = mat x.ρ g := fun g => rho1_map_ddBaseRingHom_eq_mat_rho k g
  have hinv : ∀ g : F.G₀, mat x.ρ g⁻¹ * mat x.ρ g = 1 := fun g => by
    rw [← map_mul, inv_mul_cancel, map_one]
  have comm_of : ∀ W : Matrix (Fin n) (Fin n) x.A, (∀ g, mat x.ρ g * W * mat x.ρ g⁻¹ = W) →
      ∀ g, mat x.ρ g * W = W * mat x.ρ g := by
    intro W hW g
    calc mat x.ρ g * W = mat x.ρ g * W * (mat x.ρ g⁻¹ * mat x.ρ g) := by rw [hinv, Matrix.mul_one]
      _ = W * mat x.ρ g := by rw [← Matrix.mul_assoc, hW]
  have hA : Z.map DD.a = 0 := by
    apply skew_commuting_matrix_zero x hl
    · apply comm_of
      intro g
      have := congrArg (fun M => M.map DD.a) (hZ g)
      simpa only [map_a_mul_eq_map_a_mul_map_a, hA0] using this
    · refine Matrix.ext fun r c => ?_
      have h1 := congrFun (congrFun ht r) c
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
      simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply, h1, DD.neg_a]
  have hE : ∀ t : Fin k.g, Z.map (fun y => y.ep t) = 0 := by
    intro t
    apply skew_commuting_matrix_zero x hl
    · apply comm_of
      intro g
      have := congrArg (fun M => M.map (fun y => y.ep t)) (hZ g)
      simp only [map_ep_mul_eq_leibniz, map_a_mul_eq_map_a_mul_map_a, hA0, hA, Matrix.mul_zero, Matrix.zero_mul, zero_add,
        add_zero] at this
      exact this
    · refine Matrix.ext fun r c => ?_
      have h1 := congrFun (congrFun ht r) c
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h1
      simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply, h1, DD.neg_ep]
  refine Matrix.ext fun r c => ?_
  have hm' : (Z r c).ep' = 0 ∧ (Z r c).eta = 0 := by
    obtain ⟨h1, h2⟩ := (show ∀ i j : Fin n, _ from hm) r c
    by_cases hb : (↑r < x.a ↔ ↑c < x.a)
    · obtain ⟨-, -, h3, h4⟩ := h1 hb
      exact ⟨h3 rfl, h4 rfl⟩
    · obtain ⟨-, -, h3, h4⟩ := h2 hb
      exact ⟨h3 rfl, h4 rfl⟩
  rw [Matrix.zero_apply]
  refine DD.ext ?_ (funext fun t => ?_) ?_ ?_
  · simpa using congrFun (congrFun hA r) c
  · simpa using congrFun (congrFun (hE t) r) c
  · exact hm'.1
  · exact hm'.2

private def ddMapRingHom {A X : Type} [CommRing A] [CommRing X] (g : ℕ) (f : A →+* X) : DD A g →+* DD X g where
  toFun y := ⟨f y.a, fun j => f (y.ep j), fun j => f (y.ep' j), f y.eta⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

private theorem rho1_map_ddMapRingHom_eq_rho1 {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x)
    (X : Type) [CommRing X] [Algebra x.A X] (g : F.G₀) :
    (k.ρ1 x.A g).map (ddMapRingHom k.g (algebraMap x.A X)) = k.ρ1 X g := by
  have hr : ∀ y, ddMapRingHom k.g (algebraMap x.A X) y = ⟨algebraMap x.A X y.a, fun j => algebraMap x.A X (y.ep j), fun j => algebraMap x.A X (y.ep' j), algebraMap x.A X y.eta⟩ := fun _ => rfl
  have hb : ∀ (Y : Type) [CommRing Y] [Algebra x.A Y] (y : x.A), algebraMap x.A (DD Y k.g) y = ⟨algebraMap x.A Y y, 0, 0, 0⟩ := fun _ _ _ _ => rfl
  rw [Kap.ρ1, Kap.ρ1, Matrix.map_mul]
  congr 1
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply]
    by_cases hij : i = j
    · subst hij
      refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, DD.epM, DD.add_ep, DD.one_ep, DD.add_ep', DD.one_ep', DD.add_a, DD.add_eta, DD.one_eta, DD.one_a]
    · refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, DD.epM, hij, DD.zero_ep, DD.zero_a]
  · refine Matrix.ext fun i j => ?_
    refine DD.ext ?_ (funext fun t => ?_) (funext fun t => ?_) ?_ <;> simp [hr, hb, NP.ρX]

theorem UpperTheory.V.Pa.h0G :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x), l ≠ 2 → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.M1 (x.Am m) ∧ Yᵀ = -Y ∧ ∀ g : G0.G₀, k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹ = Y}.ncard ≤ Nat.card x.K ^ C := by
  intro l _ L G G0 h n x k hl
  obtain ⟨C, hC⟩ := fixBd l G0.frame n x k (k.M1 x.A) true false false false false true false false
    G0.G₀ (fun _ => 1) (fun s => k.ρ1 x.A s) (fun s => k.ρ1 x.A s⁻¹) true rfl
  refine ⟨C, fun m => ?_⟩
  have hfin : ∀ W : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)), W = ⊥ →
      Nat.card x.K ^ (m * Module.finrank x.A W + C) = Nat.card x.K ^ C := by
    rintro W rfl
    simp
  refine le_trans (le_of_eq ?_) ((hC m).trans (le_of_eq (hfin _ ?_)))
  · clear hC hfin
    congr 1
    ext Y
    have hred : ∀ s : G0.G₀, ((k.ρ1 x.A s).map fun y : DD x.A k.g =>
        (⟨(algebraMap x.A (x.Am m)) y.a, fun j => (algebraMap x.A (x.Am m)) (y.ep j),
          fun j => (algebraMap x.A (x.Am m)) (y.ep' j), (algebraMap x.A (x.Am m)) y.eta⟩ : DD (x.Am m) k.g))
        = k.ρ1 (x.Am m) s :=
      fun s => rho1_map_ddMapRingHom_eq_rho1 k (x.Am m) s
    simp only [Set.mem_setOf_eq, one_smul, forall_const, hred]
    exact Iff.rfl
  · rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_bot]
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, ↓reduceIte] at hZ
    obtain ⟨⟨hm, ht⟩, hfix⟩ := hZ
    apply skew_invariant_M1_zero k hl Z hm
    · simpa [add_eq_zero_iff_eq_neg] using ht
    · intro g
      have := hfix g
      simpa [sub_eq_zero, Matrix.mul_assoc] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.GaloisLiftMemFirstOrderDeformations
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section Parts

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}

private abbrev SS (n a : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2 ∧ ((p.1 : ℕ) < a ↔ (p.2 : ℕ) < a)}

private abbrev TT (n a : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2 ∧ ¬ ((p.1 : ℕ) < a ↔ (p.2 : ℕ) < a)}

private def upM (f : (SS n a → X) × (TT n a → Fin g → X)) : Matrix (Fin n) (Fin n) (DD X g) :=
  Matrix.of fun i j => ⟨if h : i < j ∧ ((i : ℕ) < a ↔ (j : ℕ) < a) then f.1 ⟨(i, j), h⟩ else 0,
    if h : i < j ∧ ¬ ((i : ℕ) < a ↔ (j : ℕ) < a) then f.2 ⟨(i, j), h⟩ else 0, 0, 0⟩

end Parts
end

