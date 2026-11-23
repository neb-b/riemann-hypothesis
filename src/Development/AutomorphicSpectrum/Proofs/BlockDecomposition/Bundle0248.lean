module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinorGroupMul
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal.JacAlg

def minorGroup {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) : AddSubgroup B :=
  AddSubgroup.closure {y | ∃ (b : A) (bs : Fin m → A),
    y = ρ b * (Matrix.of fun k l => D (κ k) (ρ (bs l))).det}

theorem minorGroup_mul {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) (a : A) {y : B}
    (hy : y ∈ minorGroup ρ D κ) : ρ a * y ∈ minorGroup ρ D κ := by
  unfold minorGroup at hy ⊢
  refine AddSubgroup.closure_induction (fun z hz => ?_) ?_
    (fun z₁ z₂ _ _ h₁ h₂ => ?_) (fun z _ hz => ?_) hy
  · obtain ⟨b, bs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a * b, bs, by rw [map_mul, mul_assoc]⟩
  · rw [mul_zero]
    exact zero_mem _
  · rw [mul_add]
    exact add_mem h₁ h₂
  · rw [mul_neg]
    exact neg_mem hz

theorem leibniz_pow {R : Type} [CommRing R] (q : R → R)
    (hmul : ∀ x y, q (x * y) = x * q y + y * q x) (φ : R) (N : ℕ) :
    q (φ ^ N) = (N : R) * φ ^ (N - 1) * q φ := by
  induction N with
  | zero =>
    have h1 := hmul 1 1
    simp only [mul_one, one_mul] at h1
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -h1
  | succ n ih =>
    rw [pow_succ, hmul, ih]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring

theorem column_clear {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw]
    (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A)
    (hc : μ.comp ι = lam.comp ρ) {d : ℕ} (D : Fin d → B → B) (p : Fin d → Bw → Bw)
    (hmul : ∀ k x y, p k (x * y) = x * p k y + y * p k x)
    (hD : ∀ k x, p k (lam x) = lam (D k x))
    (a : Af) (b : A) (N : ℕ) (hb : ι f ^ N * a = ι b) (k : Fin d) :
    lam (ρ (f ^ N) * D k (ρ b) + ρ (-(N : A) * f ^ (N - 1) * b) * D k (ρ f))
      = (lam (ρ f)) ^ (2 * N) * p k (μ a) := by
  have e1 : ∀ x, μ (ι x) = lam (ρ x) := fun x => by
    simpa using RingHom.congr_fun hc x
  have hF : lam (ρ f) ^ N * μ a = lam (ρ b) := by
    have h1 := congrArg μ hb
    rwa [map_mul, map_pow, e1, e1] at h1
  have hp1 := hmul k (lam (ρ f) ^ N) (μ a)
  rw [hF, hD, leibniz_pow (p k) (hmul k) (lam (ρ f)) N, hD] at hp1
  simp only [map_add (f := _), map_mul, map_neg, map_pow, map_natCast]
  rw [hp1, ← hF]
  ring

theorem det_mem {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) (f : A) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) (c₁ c₂ b : Fin m → A) :
    (Matrix.of fun k l => ρ (c₁ l) * D (κ k) (ρ (b l))
      + ρ (c₂ l) * D (κ k) (ρ f)).det ∈ minorGroup ρ D κ := by
  classical
  unfold minorGroup
  set X : Fin m → Fin m → B := fun l k => ρ (c₁ l) * D (κ k) (ρ (b l)) with hX
  set Y : Fin m → Fin m → B := fun l k => ρ (c₂ l) * D (κ k) (ρ f) with hY
  have h1 : (Matrix.of fun k l => ρ (c₁ l) * D (κ k) (ρ (b l))
      + ρ (c₂ l) * D (κ k) (ρ f)).det = Matrix.det (Matrix.of fun l k => (X + Y) l k) := by
    rw [← Matrix.det_transpose]
    rfl
  have h2 : Matrix.det (Matrix.of fun l k => (X + Y) l k) =
      ∑ s : Finset (Fin m), Matrix.det (Matrix.of fun l k => s.piecewise X Y l k) :=
    (Matrix.detRowAlternating (n := Fin m) (R := B)).toMultilinearMap.map_add_univ X Y
  rw [h1, h2]
  refine AddSubgroup.sum_mem _ fun s _ => AddSubgroup.subset_closure ?_
  refine ⟨∏ l, (if l ∈ s then c₁ l else c₂ l), fun l => if l ∈ s then b l else f, ?_⟩
  rw [map_prod, ← Matrix.det_transpose (Matrix.of fun k l =>
      D (κ k) (ρ ((fun l => if l ∈ s then b l else f) l))),
    ← Matrix.det_mul_column]
  congr 1
  ext l k
  by_cases hl : l ∈ s <;> simp [hl, hX, hY, Finset.piecewise, Matrix.transpose_apply]

theorem det_clear {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw]
    (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A)
    (hc : μ.comp ι = lam.comp ρ) (hloc : ∀ a : Af, ∃ (b : A) (N : ℕ), ι f ^ N * a = ι b)
    {d m : ℕ} (D : Fin d → B → B) (p : Fin d → Bw → Bw)
    (hmul : ∀ k x y, p k (x * y) = x * p k y + y * p k x)
    (hD : ∀ k x, p k (lam x) = lam (D k x))
    (κ : Fin m → Fin d) (u : Fin m → Af) :
    ∃ (M : ℕ) (n : B), n ∈ minorGroup ρ D κ ∧
      (lam (ρ f)) ^ M * (Matrix.of fun k l => p (κ k) (μ (u l))).det = lam n := by
  classical
  choose bb NN hbN using hloc
  obtain ⟨N, hN⟩ : ∃ N, ∀ l, NN (u l) ≤ N :=
    ⟨Finset.univ.sup fun l => NN (u l), fun l => Finset.le_sup (f := fun l => NN (u l))
      (Finset.mem_univ l)⟩
  let b : Fin m → A := fun l => f ^ (N - NN (u l)) * bb (u l)
  have hb : ∀ l, ι f ^ N * u l = ι (b l) := by
    intro l
    simp only [b, map_mul, map_pow]
    rw [← hbN (u l), ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hN l)]
  have hcol : ∀ k l, lam (ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f))
      = lam (ρ f) ^ (2 * N) * p (κ k) (μ (u l)) :=
    fun k l => column_clear ρ lam ι μ f hc D p hmul hD (u l) (b l) N (hb l) (κ k)
  refine ⟨2 * N * m, (Matrix.of fun k l => ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f)).det,
    det_mem ρ f D κ (fun _ => f ^ N) (fun l => -(N : A) * f ^ (N - 1) * b l) b, ?_⟩
  rw [RingHom.map_det]
  have hmat : lam.mapMatrix (Matrix.of fun k l => ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f)) =
      Matrix.of fun k l => (fun _ => lam (ρ f) ^ (2 * N)) k * p (κ k) (μ (u l)) := by
    ext k l
    first
      | exact hcol k l
      | simpa using hcol k l
  rw [hmat, Matrix.det_mul_column, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul]
  rfl

theorem clear_sum : ∀ {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw] (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A),
    μ.comp ι = lam.comp ρ → (∀ a : Af, ∃ (b : A) (N : ℕ), ι f ^ N * a = ι b) → (∀ x : B, lam x = 0 → ∃ N : ℕ, ρ f ^ N * x = 0) →
    ∀ {d m : ℕ} {Λ : Type} [Fintype Λ] (D : Fin d → B → B) (p : Fin d → Bw → Bw), (∀ k x y, p k (x + y) = p k x + p k y) →
      (∀ k x y, p k (x * y) = x * p k y + y * p k x) → (∀ k x, p k (lam x) = lam (D k x)) →
      ∀ (κ : Fin m → Fin d) (z : Λ → Af) (u : Λ → Fin m → Af) (x : B),
        lam x = ∑ L, μ (z L) * (Matrix.of fun k l => p (κ k) (μ (u L l))).det →
        ∃ M : ℕ, ρ f ^ M * x ∈ AddSubgroup.closure {y | ∃ (b : A) (bs : Fin m → A), y = ρ b * (Matrix.of fun k l => D (κ k) (ρ (bs l))).det} := by
  intro A B Af Bw _ _ _ _ ρ lam ι μ f hc hloc hker d m Λ _ D p _ hmul hD κ z u x hx
  classical
  have e1 : ∀ a : A, μ (ι a) = lam (ρ a) := fun a => by
    simpa using RingHom.congr_fun hc a
  choose MM nn hnn hMM using fun L => det_clear ρ lam ι μ f hc hloc D p hmul hD κ (u L)
  choose bz Nz hz using fun L => hloc (z L)
  obtain ⟨K, hK⟩ : ∃ K, ∀ L, MM L + Nz L ≤ K :=
    ⟨Finset.univ.sup fun L => MM L + Nz L, fun L => Finset.le_sup (f := fun L => MM L + Nz L)
      (Finset.mem_univ L)⟩
  let e : Λ → A := fun L => f ^ (K - (MM L + Nz L)) * bz L
  have hterm : ∀ L, lam (ρ f) ^ K * (μ (z L) * (Matrix.of fun k l => p (κ k) (μ (u L l))).det)
      = lam (ρ (e L) * nn L) := by
    intro L
    have hzL : lam (ρ f) ^ Nz L * μ (z L) = lam (ρ (bz L)) := by
      have h1 := congrArg μ (hz L)
      rwa [map_mul, map_pow, e1, e1] at h1
    have hK' : K = (K - (MM L + Nz L)) + Nz L + MM L := by
      have h := Nat.sub_add_cancel (hK L)
      rw [add_assoc, add_comm (Nz L) (MM L), h]
    simp only [e, map_mul, map_pow, ← hzL, ← hMM L]
    conv_lhs => rw [hK', pow_add, pow_add]
    ring
  have hymem : (∑ L, ρ (e L) * nn L) ∈ minorGroup ρ D κ :=
    AddSubgroup.sum_mem _ fun L _ => minorGroup_mul ρ D κ (e L) (hnn L)
  have h0 : lam (ρ f ^ K * x - ∑ L, ρ (e L) * nn L) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_mul, map_pow, hx, Finset.mul_sum, map_sum]
    simp only [hterm]
    exact sub_self _
  obtain ⟨N', hN'⟩ := hker _ h0
  refine ⟨N' + K, ?_⟩
  have h2 : ρ f ^ (N' + K) * x = ρ (f ^ N') * ∑ L, ρ (e L) * nn L := by
    rw [pow_add, mul_assoc, ← sub_eq_zero, map_pow, ← mul_sub]
    exact hN'
  rw [h2]
  exact minorGroup_mul ρ D κ (f ^ N') hymem

end GlobalTheory.CompanionTheory.ConeLocal.JacAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherianIdealIntegralOrSplit
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.Dich

open TopologicalSpace Scheme.IdealSheafData

theorem isReduced_subscheme_of_radical_eq {X : Scheme.{0}} (J : X.IdealSheafData)
    (h : J.radical = J) : IsReduced J.subscheme := by
  have : ∀ U, IsReduced (J.subschemeCover.openCover.X U) := fun U => by
    refine (affine_isReduced_iff (.of (Γ(X, U.1) ⧸ J.ideal U))).mpr ?_
    refine (Ideal.isRadical_iff_quotient_reduced _).mp ?_
    have e : (J.ideal U).radical = J.ideal U := congr($(h).ideal U)
    exact Ideal.radical_eq_iff.mp e
  exact IsReduced.of_openCover _ J.subschemeCover.openCover

theorem irreducibleSpace_subscheme {X : Scheme.{0}} (J : X.IdealSheafData)
    (h : IsIrreducible (J.support : Set X)) : IrreducibleSpace J.subscheme := by
  have hr : Set.range J.subschemeι = (J.support : Set X) := J.range_subschemeι
  have hirr : IsIrreducible (Set.range J.subschemeι) := hr ▸ h
  have : IrreducibleSpace (Set.range J.subschemeι) :=
    { toPreirreducibleSpace := Subtype.preirreducibleSpace hirr.2
      toNonempty := hirr.1.to_subtype }
  exact J.subschemeι.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this

theorem exists_radical_pow_le {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData) :
    ∃ k : ℕ, J.radical ^ k ≤ J := by
  have hU : ∀ U : X.affineOpens, ∃ k : ℕ, (J.ideal U).radical ^ k ≤ J.ideal U := fun U => by
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    exact Ideal.exists_radical_pow_le_of_fg _ (IsNoetherian.noetherian _)
  choose k hk using hU
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.2) (fun x _ => by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t.sup k, le_of_iSup_eq_top (fun i : t => i.1) ?_ fun i => ?_⟩
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
  · change (J.ideal i.1).radical ^ t.sup k ≤ J.ideal i.1
    exact (Ideal.pow_le_pow_right (Finset.le_sup i.2)).trans (hk i.1)

theorem exists_of_radical_ne {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData)
    (hJ : J ≠ ⊤) (hr : J.radical ≠ J) :
    ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)),
      a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  classical
  have hex := exists_radical_pow_le J
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m, J.radical ^ (m + 1) ≤ J ∧ ¬ J.radical ^ m ≤ J := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hk | hk
    · have hs := Nat.find_spec hex
      rw [hk, pow_zero] at hs
      exact absurd (top_le_iff.mp hs) hJ
    · refine ⟨Nat.find hex - 1, ?_, Nat.find_min hex (by omega)⟩
      rw [Nat.sub_add_cancel hk]
      exact Nat.find_spec hex
  refine ⟨J.radical, J ⊔ J.radical ^ m, lt_of_le_of_ne J.le_radical hr.symm,
    left_lt_sup.mpr hm₂, fun U a b ha hb => ?_⟩
  have hle : J.radical.ideal U * (J ⊔ J.radical ^ m).ideal U ≤ J.ideal U := by
    change J.radical.ideal U * (J.ideal U ⊔ (J.radical.ideal U) ^ m) ≤ J.ideal U
    rw [Ideal.mul_sup]
    refine sup_le Ideal.mul_le_right ?_
    rw [← pow_succ']
    exact hm₁ U
  exact hle (Ideal.mul_mem_mul ha hb)

theorem exists_of_not_preirreducible {X : Scheme.{0}} (J : X.IdealSheafData)
    (hr : J.radical = J) (hirr : ¬ IsPreirreducible (J.support : Set X)) :
    ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)),
      a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
  push_neg at hirr
  obtain ⟨Z₁, Z₂, h₁, h₂, hcov, hn₁, hn₂⟩ := hirr
  let C₁ : Closeds X := J.support ⊓ ⟨Z₁, h₁⟩
  let C₂ : Closeds X := J.support ⊓ ⟨Z₂, h₂⟩
  have hsup : C₁ ⊔ C₂ = J.support := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    rcases hcov hx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hlt : ∀ (C : Closeds X) (Z : Set X), C ≤ J.support → (C : Set X) ⊆ Z →
      ¬ (J.support : Set X) ⊆ Z → J < vanishingIdeal C := by
    intro C Z hC hCZ hn
    refine lt_of_le_not_ge (le_support_iff_le_vanishingIdeal.mp hC) fun hle => hn ?_
    intro x hx
    have hx' : x ∈ ((vanishingIdeal C).support : Set X) := support_antitone hle hx
    rw [coe_support_vanishingIdeal] at hx'
    exact hCZ hx'
  refine ⟨vanishingIdeal C₁, vanishingIdeal C₂, hlt C₁ Z₁ inf_le_left (fun x hx => hx.2) hn₁,
    hlt C₂ Z₂ inf_le_left (fun x hx => hx.2) hn₂, fun U a b ha hb => ?_⟩
  have e : vanishingIdeal C₁ ⊓ vanishingIdeal C₂ = J := by
    rw [← vanishingIdeal_sup, hsup, vanishingIdeal_support, hr]
  have hm : a * b ∈ (vanishingIdeal C₁ ⊓ vanishingIdeal C₂).ideal U :=
    ⟨Ideal.mul_mem_right _ _ ha, Ideal.mul_mem_left _ _ hb⟩
  rwa [e] at hm

theorem isIntegral_or_exists_mul_mem : ∀ {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData),
    J ≠ ⊤ → IsIntegral J.subscheme ∨ ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧
      ∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U →
        a * b ∈ J.ideal U := by
  intro X _ J hJ
  by_cases hr : J.radical = J
  · by_cases hirr : IsPreirreducible (J.support : Set X)
    · left
      have hne : (J.support : Set X).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro h
        exact hJ (J.support_eq_bot_iff.mp (SetLike.coe_injective h))
      haveI := isReduced_subscheme_of_radical_eq J hr
      haveI := irreducibleSpace_subscheme J ⟨hne, hirr⟩
      exact isIntegral_of_irreducibleSpace_of_isReduced _
    · exact Or.inr (exists_of_not_preirreducible J hr hirr)
  · exact Or.inr (exists_of_radical_ne J hJ hr)

end GlobalTheory.CompanionTheory.GE.Dich
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmMorImg
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

universe w w' v u v' u'

namespace GlobalTheory.CompanionTheory.CrisFil

section General

variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

def subMor (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) :
    CH.Mor S.fn S'.fn σ where
  G := m.G
  τ T := ((m.τ T).domRestrict (S.S (m.G.obj T))).codRestrict (S'.S T) fun x => h T x.1 x.2
  nat φ x := Subtype.ext (m.nat φ x.1)

theorem pull_inc (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) (n : ℕ) (y : CH.H S.fn n) :
    m.pull n (S.inc.pull n y) = S'.inc.pull n ((subMor m S S' h).pull n y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

theorem pull_img (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) (n : ℕ) (x : CH.H F n)
    (hx : x ∈ S.img n) : m.pull n x ∈ S'.img n := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(subMor m S S' h).pull n y, (pull_inc m S S' h n y).symm⟩

end General

section Thick

variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R}

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}

theorem omMor_img (m : GlobalTheory.LogCris.Mor L L' σ) (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a)) (r j : ℕ)
    (x : CH.H (OM L c) j) (hx : x ∈ (pdS L c r).img j) : (omMor m σ₀ h).pull j x ∈ (pdS L' c' r).img j :=
  pull_img (omMor m σ₀ h) (pdS L c r) (pdS L' c' r) (fun _ _ hz => hz) j x hx

end Thick

theorem red_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m)
    (r j : ℕ), ∀ x ∈ HcFil F κ k m r j, redHc F κ k h j x ∈ HcFil F κ k n r j := by
  intro l _ O _ F κ k m n h r j x hx
  exact omMor_img _ _ _ r j x hx

end GlobalTheory.CompanionTheory.CrisFil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct

namespace GlobalTheory.CompanionTheory.GE

variable {X Z : Scheme.{0}}

def secsSub {E : X.Modules} (S : Subobject E) (V : X.Opens) : Submodule Γ(X, V) Γ(E, V) where
  carrier := secs S V
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro r _ ⟨a, rfl⟩
    exact ⟨r • a, Scheme.Modules.Hom.app_smul _ _ _⟩

def pullSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [Z.Over (Spec (.of A))]
    (φ : Z ⟶ X) (E : X.Modules) (S : ℕ → Subobject E) (e : ℕ) :
    Subobject ((Scheme.Modules.pullback φ).obj E) :=
  imageSubobject ((Scheme.Modules.pullback φ).map (S e).arrow) ⊔ powSub I _ (e + 1)

def adjMap (φ : Z ⟶ X) {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)) :
    E ⟶ (Scheme.Modules.pushforward φ).obj (cokernel B.arrow) :=
  (Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv E (cokernel B.arrow) (cokernel.π B.arrow)

def adjKer (φ : Z ⟶ X) {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)) :
    Subobject E :=
  kernelSubobject (adjMap φ B)

def ChartIn (φ : Z ⟶ X) (V : X.Opens) {N : Type} [AddCommGroup N] [Module Γ(X, V) N]
    (T : Submodule Γ(X, V) N) (x : N) : Prop :=
  ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ φ ⁻¹ᵁ V,
    letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
    x ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U)) ∈ LinearMap.range (T.subtype.rTensor Γ(Z, U))

def powIdeal (J₀ : X.IdealSheafData) (m : ℕ) : X.IdealSheafData where
  ideal U := J₀.ideal U ^ m
  map_ideal_basicOpen U f := by
    rw [Ideal.map_pow, J₀.map_ideal_basicOpen]
    rfl

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullCup
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CupBeta
open CrystallineSemistableComparison.CH
universe w u v u' v'

theorem pull_cup {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w} R) (m : Mor (modF A) (modF A') (RingHom.id R))
    (hm : ∀ T (x y : A.obj (m.G.obj T)), m.τ T ((mulP A).μ _ x y) = (mulP A').μ T (m.τ T x) (m.τ T y))
    {p q n : ℕ} (h : p + q = n) (x : H (modF A) p) (y : H (modF A) q) :
    m.pull n ((mulP A).cup h x y) = (mulP A').cup h (m.pull p x) (m.pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (mulP A) (mulP A') m.G m.τ m.τ m.τ m.nat m.nat m.nat hm h x y

theorem beta_cup {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) {i j m : ℕ}
    (h : i + j = m) (x : Hc F κ k n i) (y : Hc F κ k n j) :
    β F κ k n m ((CH.mulP (OcA F κ k n)).cup h x y) =
      (CH.mulP (AcrEl (F.pt κ) n)).cup h (β F κ k n i x) (β F κ k n j y) :=
  pull_cup (OcA F κ k n) (AcrEl (F.pt κ) n) (βMor F κ k n) (fun _ _ _ => rfl) h x y

end GlobalTheory.CompanionTheory.CupBeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapFactor
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.BetaCmp

theorem quotientMap_factor {B : Type} [CommRing B] {I J K : Ideal B} (hJ : I ≤ J) (hK : I ≤ K) (h : J ≤ K.comap (RingHom.id B))
    (w : B ⧸ I) : Ideal.quotientMap K (RingHom.id B) h (Ideal.Quotient.factor hJ w) = Ideal.Quotient.factor hK w := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  rfl

theorem pt_uJ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (A : PAlg l) (n : ℕ) (y : F.Pt.obj (CommRingCat.of A.U))
    (h : JJ false A n ≤ (JJ true A n).comap (RingHom.id _)) :
    F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap (JJ true A n) (RingHom.id _) h)) (F.Pt.map (CommRingCat.ofHom (uJ false A n)) y) =
      F.Pt.map (CommRingCat.ofHom (uJ true A n)) y := by
  have e : (Ideal.quotientMap (JJ true A n) (RingHom.id _) h).comp (uJ false A n) = uJ true A n :=
    RingHom.ext fun x => quotientMap_factor (fil_le false A n) (fil_le true A n) h _
  rw [← Functor.map_comp_apply, ← CommRingCat.ofHom_comp, e]

theorem β_cmp : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (n j : ℕ) (x : Hc F κ false n j), β F κ true n j ((cmpMor F κ n).pull j x) = β F κ false n j x := by
  intro l _ O _ F κ n j x
  have e : β F κ true n j ((cmpMor F κ n).pull j x) =
      ((cmpMor F κ n).comp (σ'' := RingHom.id _) (βMor F κ true n)).pull j x :=
    pull_pull (RingHom.id _) (cmpMor F κ n) (βMor F κ true n) j x
  refine e.trans ?_
  refine (cr_pull_eq (βMor F κ false n) ((cmpMor F κ n).comp (σ'' := RingHom.id _) (βMor F κ true n))
    (fun T => crHom (RingHom.id _) (fun _ => rfl) (T.1.obj.dp_fil_pfil n) ?_) ?_ ?_ j x).symm
  · intro h
    exact pt_uJ F T.1.obj n T.2.1 h
  · intro T T' f z; rfl
  · intro T z; rfl

end GlobalTheory.CompanionTheory.BetaCmp
end

