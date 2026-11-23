module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedOneAlt
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem cnt {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (Z B : AddSubgroup X) [Finite Z] (hB : B ≤ Z) (f : X →+ Y)
    (hf : ∀ b ∈ B, f b = 0) (S : Set Y) (hS : ∀ s ∈ S, ∃ z ∈ Z, f z = s) :
    S.Finite ∧ S.ncard * Nat.card B ≤ (Z : Set X).ncard := by
  let g : Z →+ Y := f.comp Z.subtype
  haveI : Finite g.range := Finite.of_surjective _ g.rangeRestrict_surjective
  have hsub : S ⊆ (g.range : Set Y) := fun s hs => by
    obtain ⟨z, hz, rfl⟩ := hS s hs
    exact ⟨⟨z, hz⟩, rfl⟩
  have hfin : (g.range : Set Y).Finite := Set.toFinite _
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 : S.ncard ≤ Nat.card g.range := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub hfin
  have h2 : Nat.card B ≤ Nat.card g.ker :=
    Nat.card_le_card_of_injective (fun b : B => (⟨⟨b.1, hB b.2⟩, hf b.1 b.2⟩ : g.ker))
      fun a b e => Subtype.ext (congrArg (fun t : g.ker => t.1.1) e)
  have h3 : Nat.card Z = Nat.card g.range * Nat.card g.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv]
  rw [← Nat.card_coe_set_eq (Z : Set X), SetLike.coe_sort_coe, h3]
  exact Nat.mul_le_mul h1 h2

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) :
    red m (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem UpperTheory.V.Th.selTr :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (rep : Representation O G.Γ (Mm O n m)), IsAd0 h y m rep → LC rep → Finite (Zl rep) → (trFun h y m '' Sel h y m).Finite ∧ (trFun h y m '' Sel h y m).ncard * Nat.card (Bl rep) ≤ {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}.ncard := by
  intro l _ L G G0 h O _ _ _ _ _ n y m rep hr hLC hF
  have hmul : ∀ g g', y.ρm h m (g * g') = y.ρm h m g * y.ρm h m g' := fun g g' => by
    simp only [Pt.ρm, map_mul, red_mul]
  have hone : y.ρm h m 1 = 1 := by simp only [Pt.ρm, map_one, red_one]
  have hrep : ∀ (g : G.G₀) Z, rep g Z = y.ρm h m g * Z * y.ρm h m g⁻¹ := fun g Z => (hr.1 g Z).trans (one_smul _ _)
  have hφ : ∀ v g, h.p₀ (G.φ v g) = G0.φ v g := fun v g => Subtype.ext (h.φ v g)
  have hρ : ∀ v g, y.ρm h m (G.φ v g) = y.ρ0 m (G0.φ v g) := fun v g => by rw [Pt.ρm, hφ]; rfl
  have hρ' : ∀ v g, y.ρm h m (G.φ v g)⁻¹ = y.ρ0 m (G0.φ v g)⁻¹ := fun v g => by rw [← map_inv, hρ, map_inv]
  let Z : AddSubgroup (G.Γ → Mm O n m) :=
    { carrier := {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}
      add_mem' := by
        rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
        exact ⟨add_mem a1 b1, fun v => add_mem (a2 v) (b2 v), fun u g hg => by rw [Pi.add_apply, a3 u g hg, b3 u g hg, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun v => zero_mem _, fun _ _ _ => rfl⟩
      neg_mem' := by
        rintro a ⟨a1, a2, a3⟩
        exact ⟨neg_mem a1, fun v => neg_mem (a2 v), fun u g hg => by rw [Pi.neg_apply, a3 u g hg, neg_zero]⟩ }
  haveI : Finite Z := Finite.of_injective (fun z : Z => (⟨z.1, z.2.1⟩ : Zl rep))
    fun a b e => Subtype.ext (congrArg (fun t : Zl rep => t.1) e)
  let f : (G.Γ → Mm O n m) →+ (G.G₀ → Om O m) :=
    { toFun := fun z => trFun h y m fun g => z g
      map_zero' := funext fun g => by simp [trFun]
      map_add' := fun a b => funext fun g => by simp [trFun, Matrix.add_mul] }
  refine cnt Z (Bl rep).toAddSubgroup (fun b hb => ?_) f (fun b hb => ?_) _ ?_
  · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hb
    obtain rfl : b = fun g => rep g Y - Y := funext hY
    refine ⟨⟨(hLC Y).comp (· - Y), fun g g' => by simp only [map_mul, Module.End.mul_apply, map_sub]; abel⟩,
      fun v => AddSubgroup.mem_sup_left ((mem_Bl _).2 ⟨Y, fun g => rfl⟩), fun u g hg => ?_⟩
    have e : y.ρ (h.p₀ (G.φu u g)) = 1 := y.ine u _ ⟨g, hg, Subtype.ext (h.φu u g).symm⟩
    have e1 : y.ρm h m (G.φu u g) = 1 := by rw [Pt.ρm, mat, MonoidHom.comp_apply, e, map_one, red_one]
    have e2 : y.ρm h m (G.φu u g)⁻¹ = 1 := by
      rw [Pt.ρm, map_inv, mat, MonoidHom.comp_apply, map_inv, e, inv_one, map_one, red_one]
    show rep (G.φu u g : G.G₀) Y - Y = 0
    rw [hrep, e1, e2, one_mul, mul_one, sub_self]
  · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hb
    funext g
    show (b g * y.ρm h m g).trace = 0
    rw [hY, hrep, sub_mul, mul_assoc _ _ (y.ρm h m g), ← hmul, inv_mul_cancel, hone, mul_one, Matrix.trace_sub,
      Matrix.trace_mul_comm, sub_self]
  · rintro _ ⟨z, ⟨z1, z2, z3, z4, z5⟩, rfl⟩
    have hP : IsUnit (red m (y.P : Matrix (Fin n) (Fin n) O)) :=
      ⟨⟨red m (y.P : Matrix (Fin n) (Fin n) O), red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O), by rw [← red_mul, Units.mul_inv, red_one],
        by rw [← red_mul, Units.inv_mul, red_one]⟩, rfl⟩
    obtain ⟨z', h1, -, h3⟩ := (polP l G.frame O (Om O m) n _ _ _ rep hP hr).1 z z1
      (fun g g' => by rw [one_smul]; exact z2 g g') (fun g => by rw [one_smul]; exact z3 g)
    refine ⟨z', ⟨h1, fun v => ?_, fun u g hg => (h3 _).trans (z4 u _ ⟨g, hg, rfl⟩)⟩, funext fun g => by
      show (z' g * _).trace = (z g * _).trace
      rw [h3]⟩
    obtain ⟨Y, hY⟩ := z5 v
    have hc : Continuous (G.η.ker.subtype.comp (G.φ v)) := continuous_subtype_val.comp (G.φ_cont v)
    have e : z' ∘ (G.η.ker.subtype.comp (G.φ v)) = (fun g => rep (G.φ v g : G.G₀) Y - Y) +
        fun g => z' (G.φ v g : G.G₀) - (rep (G.φ v g : G.G₀) Y - Y) := funext fun g => by simp
    rw [e]
    refine AddSubgroup.add_mem_sup ((mem_Bl _).2 ⟨Y, fun g => rfl⟩) ⟨?_, fun g g' => ?_, fun g => ?_⟩
    · exact (h1.1.comp_continuous hc).sub (((hLC Y).comp_continuous hc).comp (· - Y))
    · rw [← hρ, ← hρ', ← hrep]
      beta_reduce
      rw [map_mul, Subgroup.coe_mul, h1.2, map_mul, Module.End.mul_apply, map_sub, map_sub]
      abel
    · have := (hY g).1
      rw [dY, ← hrep] at this
      simp only [h3]
      exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedSurj
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem red_mul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_sub' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A - B) = red m A - red m B := by
  ext i j
  simp [red]

private theorem red_surj {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (Y : Mm O n m) : ∃ Y', red m Y' = Y := by
  choose Y' hY' using fun i j => Ideal.Quotient.mk_surjective (Y i j)
  exact ⟨Matrix.of Y', by ext i j; exact hY' i j⟩

private theorem red_add' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A + B) = red m A + red m B := by
  ext i j
  simp [red]

theorem UpperTheory.V.Th.h0GO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n), l ≠ 2 → ∃ C : ℕ, ∀ m, {Y : Mm O n m | red m y.P * Y = -(Yᵀ * red m y.P) ∧ ∀ g, y.ρ0 m g * Y * y.ρ0 m g⁻¹ = Y}.ncard ≤ Nat.card (ResidueField O) ^ C := by
  intro l _ L G0 O _ _ _ hO _ n y hl
  have h2u : IsUnit (2 : O) := (omFacts l O).1 hl
  let Φ : Option G0.G₀ → Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O := fun s => s.elim
    (LinearMap.mulLeft O (y.P : Matrix (Fin n) (Fin n) O) + (LinearMap.mulRight O (y.P : Matrix (Fin n) (Fin n) O)).comp
      (Matrix.transposeLinearEquiv (Fin n) (Fin n) O O).toLinearMap)
    fun g => (LinearMap.mulRight O (mat y.ρ g⁻¹)).comp (LinearMap.mulLeft O (mat y.ρ g)) - LinearMap.id
  have hΦ0 : ∀ Y, Φ none Y = (y.P : Matrix (Fin n) (Fin n) O) * Y + Yᵀ * y.P := fun _ => rfl
  have hΦ : ∀ g Y, Φ (some g) Y = mat y.ρ g * Y * mat y.ρ g⁻¹ - Y := fun _ _ => rfl
  obtain ⟨C, hC⟩ := fixCnt l O n _ Φ
  have hk : (⨅ g, LinearMap.ker (Φ g) : Submodule O (Matrix (Fin n) (Fin n) O)) = ⊥ := by
    refine eq_bot_iff.2 fun Y hY => ?_
    obtain ⟨c, hc, hsp⟩ := y.span
    have h1 : ∀ Z ∈ Submodule.span O (Set.range (mat y.ρ)), Z * Y = Y * Z := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem Z hZ =>
        obtain ⟨g, rfl⟩ := hZ
        have h1 : Φ (some g) Y = 0 := (Submodule.mem_iInf _).mp hY (some g)
        rw [hΦ, sub_eq_zero] at h1
        have h2 := congrArg (· * mat y.ρ g) h1
        simpa only [Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one] using h2
      | zero => simp
      | add a b _ _ ha hb => rw [Matrix.add_mul, Matrix.mul_add, ha, hb]
      | smul a b _ hb => rw [Matrix.smul_mul, Matrix.mul_smul, hb]
    have h2 : ∀ Z, Z * Y = Y * Z := fun Z => by
      have := h1 _ (hsp Z)
      rw [Matrix.smul_mul, Matrix.mul_smul] at this
      exact smul_right_injective _ hc this
    obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_of_commute_single (M := Y) fun i j _ => h2 _
    have h3 : Φ none Y = 0 := (Submodule.mem_iInf _).mp hY none
    have hs : Y = a • (1 : Matrix (Fin n) (Fin n) O) := by
      rw [← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have ht : Yᵀ = Y := by rw [hs, Matrix.transpose_smul, Matrix.transpose_one]
    rw [hΦ0, ht, h2, ← two_smul O, h2u.smul_eq_zero] at h3
    exact (Units.mul_left_eq_zero y.P).1 h3
  refine ⟨C, fun m => ?_⟩
  have := hC m
  rw [hk, finrank_bot, mul_zero, zero_add] at this
  refine le_trans (le_of_eq (congrArg Set.ncard ?_)) this
  have ht : ∀ Y : Matrix (Fin n) (Fin n) O, red m Yᵀ = (red m Y)ᵀ := fun _ => rfl
  ext Y
  constructor
  · rintro ⟨h0, hY⟩
    obtain ⟨Y', e⟩ := red_surj m Y
    refine ⟨Y', e, ?_⟩
    rintro (_ | g)
    · rw [hΦ0, red_add', red_mul', red_mul', ht, e, h0, neg_add_cancel]
    · rw [hΦ, red_sub', red_mul', red_mul', e]
      exact sub_eq_zero.mpr (hY g)
  · rintro ⟨Y', e, h⟩
    refine ⟨?_, fun g => ?_⟩
    · have h1 := h none
      rw [hΦ0, red_add', red_mul', red_mul', ht, e] at h1
      exact eq_neg_of_add_eq_zero_left h1
    · have h1 := h (some g)
      rw [hΦ, red_sub', red_mul', red_mul', e] at h1
      exact sub_eq_zero.mp h1
end

