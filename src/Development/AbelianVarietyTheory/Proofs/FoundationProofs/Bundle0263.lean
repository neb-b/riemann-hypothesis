module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeneralAdmissibleOfIrreducibilityStmt
section
noncomputable section

namespace GlobalTheory.TripleResidual

open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (OnW IsBaseChange IsGaloisRepOf IsReduction Zbar GaloisReps GalE toFb)
open scoped Pointwise

theorem span_eq_top_of_trace_eq {Γ K : Type} [Monoid Γ] [Field K] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) K) (h : ∀ g, (M g).trace = (N g).trace)
    (hN : Submodule.span K (Set.range N) = ⊤) : Submodule.span K (Set.range M) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq
  | exact _root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq
  | (apply _root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceFormNondegenerate.span_eq_top_of_trace_eq ..)

theorem trace_eq_of_charpoly_eq {K : Type} [Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (h : A.charpoly = B.charpoly) : A.trace = B.trace := by
  rcases n with _ | n
  · simp [Matrix.trace]
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, h]

theorem det_ne_zero_of_not_isRoot {k K : Type} [Field k] [Field K] (κ : k →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (c : k) (h : ¬ (A.map κ).charpoly.IsRoot (κ c)) :
    (A - c • (1 : Matrix _ _ k)).det ≠ 0 := by
  intro h0
  apply h
  rw [Matrix.charpoly_map, IsRoot, eval_map, eval₂_hom, Matrix.eval_charpoly, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, ← neg_sub, Matrix.det_neg, h0, mul_zero, map_zero]

theorem charpoly_conj_GL {Γ K : Type} [Group Γ] [Field K] {n : ℕ} (ρ : Γ →* GL (Fin n) K) (g s : Γ) :
    ((ρ (g * s * g⁻¹) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly =
      ((ρ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

section Wild

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def WildAt (A : ValuationSubring Ω) (u : G E Ω) : Prop := ∀ y : Ω, y ≠ 0 → A.valuation (u y / y - 1) < 1

omit [NumberField E] in
theorem wildAt_conj (c : Ω ≃+* Ω) {A : ValuationSubring Ω} {u u' : G E Ω} (h : ∀ y, u' y = c (u (c.symm y)))
    (hu : WildAt (moveVal c A) u') : WildAt A u := fun y hy => by
  have := hu (c y) ((map_ne_zero_iff _ c.injective).2 hy)
  rw [moveVal_lt_one, map_sub, map_div₀, map_one, h] at this
  simpa using this

theorem wildAt_of_isWild {A : ValuationSubring Ω} {u : G E Ω} (h : BlochKatoReduction.IsWild A u) : WildAt A u := fun y hy => by
  have e : u y / y - 1 = (u y - y) / y := by field_simp
  have h0 : 0 < A.valuation y := zero_lt_iff.mpr (by simpa using hy)
  rw [e, map_div₀, div_lt_one₀ h0]
  exact h.2 y hy

theorem mem_ine_of_wildAt {A : ValuationSubring Ω} {u : G E Ω} (h : WildAt A u) : u ∈ Ine (F := E) A :=
  (GlobalTheory.InertiaTypePrimes.isWild_of_isWildAt A u h).1

theorem eq_one_of_wildAt [IsAlgClosure E Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}
    (hA : IsPlaceOver A v) {l : ℕ} [Fact l.Prime] (hv : v ∉ placesOver E l) {K : Type} [Field K] [CharP K l] {n : ℕ}
    (ρ : G E Ω →* GL (Fin n) K) (ho : IsOpen (ρ.ker : Set (G E Ω))) {u : G E Ω} (hu : WildAt A u)
    (hc : ((ρ u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n) : ρ u = 1 := by
  refine GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ A v hA ρ.ker inferInstance ho u (l ^ n) (fun hm => hv ?_) hu ?_
  · rw [Nat.cast_pow] at hm
    exact v.isPrime.mem_of_pow_mem _ hm
  · rw [MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]
    exact pow_eq_one_of_charpoly _ hc

def TameOff {K : Type} [Field K] {n : ℕ} (ρ : G E Ω →* GL (Fin n) K) (χ : G E Ω →* Kˣ) (A : ValuationSubring Ω) :
    Prop :=
  (∀ u, WildAt A u → ρ u = 1) ∧ ∃ s ∈ Ine (F := E) A,
    ¬ ((ρ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.IsRoot ((χ s : Kˣ) : K)

theorem TameOff.move [IsAlgClosure E Ω] {K : Type} [Field K] {n : ℕ} {ρ : G E Ω →* GL (Fin n) K} {χ : G E Ω →* Kˣ}
    {A A' : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A v) (hA' : IsPlaceOver A' v)
    (h : TameOff ρ χ A) : TameOff ρ χ A' := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := E) hA hA'
  have e : moveVal g.toRingEquiv A = A' := by
    rw [← hg]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  subst e
  obtain ⟨h1, s, hs, h2⟩ := h
  refine ⟨fun u hu => ?_, g * s * g⁻¹,
    conjAut_mem_ine g.toRingEquiv (fun x => ⟨x, g.symm.commutes x⟩) hs, ?_⟩
  · have h3 := h1 (g⁻¹ * u * g) (wildAt_conj g.toRingEquiv (fun y => ?_) hu)
    · have e : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      rw [e, map_mul, map_mul, h3, mul_one, ← map_mul, mul_inv_cancel, map_one]
    · change u y = (g * (g⁻¹ * u * g) * g⁻¹) y
      congr 1
      group
  · rwa [charpoly_conj_GL, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

end Wild

section Row

variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)

theorem tameOff_all {l : ℕ} [Fact l.Prime] {k : Fin 2} (hl : l ≠ D.host.g k)
    {ρ : GalE D →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)} {χ : GalE D →* (Formalism.CyclotomicNorms.Fbar l)ˣ}
    (ho : IsOpen (ρ.ker : Set (GalE D)))
    (hρ : ∀ v, ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
      ((ρ (cConj Y s) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)).charpoly =
        ((ρ s⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)).charpoly)
    (hχ : ∀ v, ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)), χ (cConj Y s) = (χ s)⁻¹)
    (h : ∀ v, TameOff ρ χ (D.nd.plOm.1 (D.naut.plGw k v)))
    {w : PlE D.host} (hw : w ∈ placesOver D.host.E (D.host.g k)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver A w) : TameOff ρ χ A := by
  obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · exact (h v).move (D.nd.plOm.2 _) hA
  have hB := isPlaceOver_moveVal_cc Y hv (D.nd.plOm.2 _)
  refine TameOff.move hB hA ?_
  obtain ⟨h1, s, hs, h2⟩ := h v
  refine ⟨fun u hu => ?_, cConj Y s⁻¹, cConj_mem_ine Y (Subgroup.inv_mem _ hs), ?_⟩
  · have h3 : WildAt (D.nd.plOm.1 (D.naut.plGw k v)) (cConj Y u) :=
      wildAt_conj Y.cc (fun y => by rw [← cConj_apply, cConj_cConj]) hu
    have h4 := hρ v _ (mem_ine_of_wildAt h3)
    rw [cConj_cConj, map_inv, h1 _ h3, inv_one, Units.val_one, Matrix.charpoly_one, Fintype.card_fin] at h4
    exact eq_one_of_wildAt hB (fun hm => not_mem_of_ne (v := v) (Fact.out : l.Prime) hl
      (mem_placesOver_conj (isConjPl_symm hv) hm)) ρ ho hu h4
  · rwa [hρ v _ (Subgroup.inv_mem _ hs), hχ v _ (Subgroup.inv_mem _ hs), inv_inv, map_inv, inv_inv]

end Row

section Triples

variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)

abbrev FbAt (D : D7) (w : D.what₂.places.Pl) : Type :=
  Fb (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w)

def IsRowOfTriple (i : Y.Tw) (s : Y.Sig i) (σ : D.what₂.FT) (w : D.what₂.places.Pl)
    (κ : IsLocalRing.ResidueField (Y.O0 i) →+* FbAt D w) : Prop :=
  D.nd.goodRow σ ∧ D.what₂.isot (Y.jS i s) σ ≠ ⊥ ∧ D.what₂.places.resChar w = Y.l i ∧
  (∀ x : 𝓞 ↥D.LL0, (∃ y ∈ IsLocalRing.maximalIdeal (Y.O0 i), algebraMap (Y.O0 i) (FractionRing (Y.O0 i)) y =
      (if Y.side i s then Y.emb0 i else Y.emb0b i) (x : ↥D.LL0)) ↔
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL)) ∧
  (∃ η : GalE D →* (FbAt D w)ˣ,
    (∀ v, v ∉ placesOver D.host.E (Y.l i) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ t ∈ Ine (F := D.host.E) A, η t = 1) ∧
    ∀ g, ((BlochKatoReduction.Gen.rbar Y i s g).map κ).charpoly =
      (((η g : (FbAt D w)ˣ) : FbAt D w) •
        ((D.ntypes.rbar σ w g : GL (Fin D.R.r) (FbAt D w)) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w))).charpoly) ∧
  ∀ k, D.host.g k ≠ Y.l i → ∀ v : D.nd.PlG k, ∃ u : (ZMod (D.host.g k))ˣ,
    (u = D.nd.chiT k v ⟨Y.jS i s - 1, by have := Y.jS_range i s; omega⟩ ∨
      u = (D.nd.chiT k v ⟨Y.jS i s - 1, by have := Y.jS_range i s; omega⟩)⁻¹) ∧
    κ (IsLocalRing.residue (Y.O0 i) ((BlochKatoReduction.Gen.chiS i s (D.ntypes.tg k v) : (Y.O0 i)ˣ) : Y.O0 i)) =
      D.ntypes.iota k v w (toFb D k u)

def BlockCharConj : Prop :=
  ∀ i, Y.NonzeroIndexPlace i → ∀ j b, 1 ≤ j → j ≤ D.R.m → ∀ k, D.host.g k ≠ Y.l i → ∀ v ∈ placesOver D.host.E (D.host.g k),
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ t ∈ Ine (F := D.host.E) A, ∀ t' : GalE D,
      (∀ x, t' x = Y.cc (t (Y.cc.symm x))) → Y.chi1 i j b t' = (Y.chi1 i j b t)⁻¹

variable {Y}

theorem admissible_at_of_irreducible_tame {i : Y.Tw} {s : Y.Sig i} {σ : D.what₂.FT} {w : D.what₂.places.Pl}
    {κ : IsLocalRing.ResidueField (Y.O0 i) →+* FbAt D w} (h : IsRowOfTriple Y i s σ w κ)
    (hirr : @Formalism.CyclotomicNorms.IrredOn _ _ ⟨D.what₂.places.resChar_prime w⟩ _ _ (D.ntypes.rbar σ w) ⊤)
    (htame : ∀ k, D.host.g k ≠ Y.l i → ∀ v ∈ placesOver D.host.E (D.host.g k), ∀ A : ValuationSubring D.nd.Om,
      IsPlaceOver A v → TameOff (D.ntypes.rbar σ w)
        ((Units.map (κ.comp (IsLocalRing.residue (Y.O0 i))).toMonoidHom).comp (BlochKatoReduction.Gen.chiS i s)) A) :
    BlochKatoReduction.Gen.ValuationStabilityAtRing Y i s := by
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  obtain ⟨-, -, hl, -, ⟨η, hη, hcp⟩, -⟩ := h
  let ρ := mapRep (κ.comp (IsLocalRing.residue (Y.O0 i))) (Y.rhoS i s)
  have hρ : ∀ g, ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)) = (BlochKatoReduction.Gen.rbar Y i s g).map κ :=
    fun _ => rfl
  refine ⟨?_, fun k hk v hv A hA => ?_⟩
  · have hr : Nonempty (Fin D.R.r) := ⟨⟨0, (odd_r D.R).pos⟩⟩
    have h1 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub (D.ntypes.rbar σ w)
      ⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => hirr W fun g _ => hW g⟩
    have h2 := span_eq_top_of_trace_eq ((Units.coeHom _).comp ρ)
      (twistM ((Units.coeHom _).comp (D.ntypes.rbar σ w)) η) (fun g => trace_eq_of_charpoly_eq (hcp g)) (by
        rw [eq_top_iff, ← h1, Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        have := Submodule.smul_mem _ (((η g)⁻¹ : (FbAt D w)ˣ) : FbAt D w) (Submodule.subset_span (R := FbAt D w)
          (Set.mem_range_self (f := twistM ((Units.coeHom _).comp (D.ntypes.rbar σ w)) η) g))
        change (((η g)⁻¹ : (FbAt D w)ˣ) : FbAt D w) • ((η g : (FbAt D w)ˣ) : FbAt D w) •
          ((D.ntypes.rbar σ w g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)) ∈ _ at this
        rwa [smul_smul, Units.inv_mul, one_smul] at this)
    let := κ.toAlgebra
    exact GlobalTheory.BurnsideField.span_eq_top_of_span_map (K := FbAt D w) _ h2
  · have hvl : v ∉ placesOver D.host.E (Y.l i) := fun hm => by
      obtain ⟨a, b, hab⟩ : IsCoprime ((Y.l i : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) :=
        Nat.Coprime.cast ((Nat.coprime_primes (Y.lPrime i).out (D.host.g_prime k)).2 hk.symm)
      refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hv)
    obtain ⟨h1, t, ht, h2⟩ := htame k hk v hv A hA
    refine ⟨fun u hu => ?_, t, ht, det_ne_zero_of_not_isRoot κ _ _ ?_⟩
    · have hm : IsOpen (IsLocalRing.maximalIdeal (Y.O0 i) : Set (Y.O0 i)) := by
        simpa using (isAdic_iff.mp (Y.twistBaseCoefficientRing_isAdic i)).1 1
      have ho : IsOpen (ρ.ker : Set (GalE D)) := by
        refine Subgroup.isOpen_mono (fun g hg => ?_)
          (GlobalTheory.InertiaTypePrimes.isOpen_ker_mapRep _ hm _ (Y.rhoS_cont i s))
        have h3 : BlochKatoReduction.Gen.rbar Y i s g = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
        rw [MonoidHom.mem_ker, Units.ext_iff, hρ, h3, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]
      have h3 := eq_one_of_wildAt hA (hl ▸ hvl) ρ ho (wildAt_of_isWild hu) (by
        rw [hρ, hcp, hη v hvl A hA u hu.1, h1 u (wildAt_of_isWild hu), Units.val_one, Units.val_one, one_smul,
          Matrix.charpoly_one, Fintype.card_fin])
      apply Matrix.map_injective κ.injective
      change (BlochKatoReduction.Gen.rbar Y i s u).map κ = Matrix.map 1 κ
      rw [← hρ, h3, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]
    · rw [hcp, hη v hvl A hA t ht, Units.val_one, one_smul]
      exact h2

end Triples

end GlobalTheory.TripleResidual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.QuadSubfield

variable (D : D7)

theorem emb_conj (f : D.host.E →+* ℂ) (y : D.host.E) :
    f (D.host.conj y) = starRingEnd ℂ (f y) := D.host.conjE_apply f y

theorem conj_conj (y : D.host.E) : D.host.conj (D.host.conj y) = y := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

theorem exists_coords {x : D.host.E} (hx : x ∈ D.host.K) :
    ∃ a b : ℚ, x = (a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD := by
  have halg : IsAlgebraic ℚ D.host.sqrtMinusD := Algebra.IsAlgebraic.isAlgebraic _
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqrtMinusD} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hx
  clear hx
  have hs := D.host.sqrtMinusD_sq
  induction hx' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    refine ⟨a * a' - D.host.d * b * b', a * b' + a' * b, ?_⟩
    push_cast
    linear_combination (b : D.host.E) * (b' : D.host.E) * hs

theorem conj_coords (a b : ℚ) :
    D.host.conj ((a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD) =
      (a : D.host.E) - (b : D.host.E) * D.host.sqrtMinusD := by
  rw [map_add (f := _), map_mul, map_ratCast, map_ratCast, D.host.conj_sqrtMinusD]
  ring

theorem conj_mem {x : D.host.E} (hx : x ∈ D.host.K) : D.host.conj x ∈ D.host.K := by
  obtain ⟨a, b, rfl⟩ := exists_coords D hx
  rw [conj_coords]
  exact sub_mem (SubfieldClass.ratCast_mem _ a)
    (mul_mem (SubfieldClass.ratCast_mem _ b) (Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D))

def conjK : D.host.K →+* D.host.K :=
  RingHom.codRestrict ((D.host.conj : D.host.E →+* D.host.E).comp D.host.K.val.toRingHom)
    D.host.K (fun x => conj_mem D x.2)

theorem coe_conjK (x : D.host.K) : ((conjK D x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := rfl

theorem isGalois_over : IsGalois D.host.K D.host.E := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  exact IsGalois.tower_top_of_isGalois ℚ _ _

theorem coe_trace (y : D.host.E) :
    ((Algebra.trace D.host.K D.host.E y : D.host.K) : D.host.E) =
      ∑ τ : D.host.E ≃ₐ[D.host.K] D.host.E, τ y := by
  have := isGalois_over D
  exact trace_eq_sum_automorphisms (K := D.host.K) y

theorem conj_comm (τ : D.host.E ≃ₐ[D.host.K] D.host.E) (y : D.host.E) :
    D.host.conj (τ y) = τ (D.host.conj y) := by
  have h : D.host.conj * τ.restrictScalars ℚ = τ.restrictScalars ℚ * D.host.conj :=
    D.host.gal.injective (by rw [map_mul, map_mul, mul_comm])
  exact AlgEquiv.congr_fun h y

theorem trace_conj (y : D.host.E) :
    Algebra.trace D.host.K D.host.E (D.host.conj y) =
      conjK D (Algebra.trace D.host.K D.host.E y) := by
  apply Subtype.ext
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_conjK, coe_trace, coe_trace, map_sum]
  exact Finset.sum_congr rfl fun τ _ => (conj_comm D τ y).symm

theorem trace_pos (y : D.host.E) (hy : y ≠ 0) :
    ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
  obtain ⟨a, b, hab⟩ := exists_coords D (Algebra.trace D.host.K D.host.E (y * D.host.conj y)).2
  have hfix : D.host.conj ((Algebra.trace D.host.K D.host.E (y * D.host.conj y) : D.host.K) : D.host.E)
      = ((Algebra.trace D.host.K D.host.E (y * D.host.conj y) : D.host.K) : D.host.E) := by
    rw [← coe_conjK, ← trace_conj, map_mul, conj_conj, mul_comm]
  rw [hab, conj_coords] at hfix
  have hb : (b : D.host.E) * D.host.sqrtMinusD = 0 := by linear_combination (-1 / 2 : D.host.E) * hfix
  rw [hb, add_zero] at hab
  refine ⟨a, ?_, Subtype.ext (by rw [hab]; simp)⟩
  have h1 := congrArg D.host.φ₀ hab
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_trace, map_sum, map_ratCast] at h1
  have h2 : ∀ τ : D.host.E ≃ₐ[D.host.K] D.host.E,
      D.host.φ₀ (τ (y * D.host.conj y)) = ((Complex.normSq (D.host.φ₀ (τ y)) : ℝ) : ℂ) := by
    intro τ
    rw [map_mul, ← conj_comm, map_mul, emb_conj, Complex.mul_conj]
  simp only [h2] at h1
  have h3 : ∑ τ : D.host.E ≃ₐ[D.host.K] D.host.E, Complex.normSq (D.host.φ₀ (τ y)) = (a : ℝ) := by
    exact_mod_cast h1
  have h4 : (0 : ℝ) < a := by
    rw [← h3]
    refine Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ?_) Finset.univ_nonempty
    simpa using hy
  exact_mod_cast h4

theorem finrank_over : Module.finrank D.host.K D.host.E = fF D := by
  have h := Module.finrank_mul_finrank ℚ D.host.K D.host.E
  rw [Formalism.L2.Pj.LPb.finrank_K, D.host.finrank_cmField] at h
  show _ = 2 * D.R.ord
  omega

theorem quadratic_subfield : ∀ D : D7, Module.finrank D.host.K D.host.E = fF D ∧ ∃ (σ : D.host.K →+* D.host.K) (θ : D.host.K), (∀ x : D.host.K, ((σ x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E)) ∧ θ ^ 2 = -(D.host.d : D.host.K) ∧ σ θ = -θ ∧ (∀ x : D.host.K, ∃ a b : ℚ, x = (a : D.host.K) + (b : D.host.K) * θ) ∧ IsIntegral ℤ ((1 + θ) / 2) ∧ (∀ y : D.host.E, D.host.conj (D.host.conj y) = y) ∧ (∀ y : D.host.E, Algebra.trace D.host.K D.host.E (D.host.conj y) = σ (Algebra.trace D.host.K D.host.E y)) ∧ ∀ y : D.host.E, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
  intro D
  refine ⟨finrank_over D, conjK D, ⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩,
    coe_conjK D, ?_, ?_, ?_, ?_, conj_conj D, trace_conj D, trace_pos D⟩
  · apply Subtype.ext
    simpa using D.host.sqrtMinusD_sq
  · apply Subtype.ext
    rw [coe_conjK]
    exact D.host.conj_sqrtMinusD
  · intro x
    obtain ⟨a, b, h⟩ := exists_coords D x.2
    exact ⟨a, b, Subtype.ext (by simpa using h)⟩
  · have h := (Formalism.L2.Pj.LPb.w0K D).2
    convert h using 1
    first | rfl | (apply Subtype.ext; simp [Formalism.L2.Pj.LPb.w0K])

end GlobalTheory.QuadSubfield
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.DatumBasic

variable {p : ℕ} [Fact p.Prime]

theorem wModel_Δ (lam : Qbar →+* ℂ_[p]) {Λ : AddSubgroup ℂ} (h2 : g2 Λ ∈ Qbar) (h3 : g3 Λ ∈ Qbar)
    (hd : TaylorLogMetric.discr Λ = 1) : (wModel lam Λ).Δ = 1 := by
  set a : Qbar := ⟨g2 Λ, h2⟩ with ha
  set b : Qbar := ⟨g3 Λ, h3⟩ with hb
  have hc : ∀ x : Qbar, lamC lam (-(x : ℂ) / 4) = -(lam x) / 4 := by
    intro x
    have e : -(x : ℂ) / 4 = ((-x / 4 : Qbar) : ℂ) := by
      push_cast
      rfl
    rw [e, lamC, dite_eq_left (-x / 4).2]
    change lam (-x / 4) = _
    rw [map_div₀, map_neg, map_ofNat]
  have e : a ^ 3 - 27 * b ^ 2 = 1 := by
    apply Subtype.ext
    push_cast
    exact hd
  have e2 := congrArg lam e
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one] at e2
  have ea := hc a
  have eb := hc b
  simp only [ha, hb] at ea eb
  simp only [wModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, ea, eb]
  linear_combination e2

theorem intSer_of_isWq {W : WeierstrassCurve ℂ_[p]} (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) {w : PowerSeries ℂ_[p]}
    (h : IsWq W w) : IntSer w := by
  obtain ⟨hr, -, hC, hX, -⟩ := SerRing.series_ring_laws p
  have hadd : ∀ {f g : PowerSeries ℂ_[p]}, IntSer f → IntSer g → IntSer (f + g) :=
    fun hf hg => (hr _ _ hf hg).1
  have hterm : ∀ (c : ℂ_[p]) (i j : ℕ) (t : PowerSeries ℂ_[p]), ‖c‖ ≤ 1 → IntSer t →
      IntSer (PowerSeries.C c * PowerSeries.X ^ i * t ^ j) := fun c i j t hc ht =>
    SerRing.intSer_mul (SerRing.intSer_mul ((hC c).2 hc) (SerRing.intSer_pow hX i))
      (SerRing.intSer_pow ht j)
  have hone : IntSer (1 : PowerSeries ℂ_[p]) := by simpa using SerRing.intSer_pow hX 0
  have key : ∀ n : ℕ, ∃ t : PowerSeries ℂ_[p], IntSer t ∧ PowerSeries.X ^ n ∣ w - t := by
    intro n
    induction n with
    | zero => exact ⟨1, hone, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht, z, hz⟩ := ih
      refine ⟨_, hadd (hadd (hadd (hadd (hadd hone (hterm _ 1 1 t h1 ht)) (hterm _ 2 1 t h2 ht))
        (hterm _ 3 2 t h3 ht)) (hterm _ 4 2 t h4 ht)) (hterm _ 6 3 t h6 ht),
        z * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2)), ?_⟩
      have h' : w = 1 + PowerSeries.C W.a₁ * PowerSeries.X * w +
          PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w + PowerSeries.C W.a₃ * PowerSeries.X ^ 3 * w ^ 2 +
          PowerSeries.C W.a₄ * PowerSeries.X ^ 4 * w ^ 2 +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 6 * w ^ 3 := h
      linear_combination h' + (PowerSeries.X * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2))) * hz
  intro n
  obtain ⟨t, ht, hd⟩ := key (n + 1)
  have e := PowerSeries.X_pow_dvd_iff.1 hd n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at e
  rw [e]
  exact ht n

theorem datum_basic : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → ‖((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ IntSer g.wq⁻¹ ∧ PowerSeries.constantCoeff g.wq⁻¹ = 1 ∧ PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  intro p _ g ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hw, _⟩ hL a2 a3 hd
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have := congrArg PowerSeries.constantCoeff hw
    simpa using this
  refine ⟨?_, SerRing.intSer_inv (intSer_of_isWq h1 h2 h3 h4 h6 hw) (by rw [hw0, norm_one]),
    by rw [PowerSeries.constantCoeff_inv, hw0, inv_one],
    GlobalTheory.ThetaParam.constantCoeff_ePhi1 g hw (GlobalTheory.OddTheta.sgStar_laws _ hL).1.2.1,
    GlobalTheory.ThetaParam.atU_sg g ((hL.sg_eq_zero 0).2 (zero_mem _))⟩
  rw [WeierstrassCurve.variableChange_Δ, wModel_Δ g.lam a2 a3 hd, mul_one, norm_pow] at hΔ
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hΔ

end GlobalTheory.EvenTheta.DatumBasic
end
end

