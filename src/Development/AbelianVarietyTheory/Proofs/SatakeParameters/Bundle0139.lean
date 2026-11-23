module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalDualPairSwapHermitianAdjoint
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem eig_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ) (σ : Weil h) :
    (WD.lpOfChar h ξ hξ).eig σ = {(ξ σ : ℂ)} := by
  rw [WD.lpOfChar, WD.eig_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

theorem cls_eq_ofChar (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1)
    (hc : Nonempty (c.π.Equiv (detRep (Fin 1) χ))) :
    ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
  obtain ⟨φ⟩ := hc
  have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
    ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
  have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
    Units.continuous_map (continuous_matrix fun i j => by
      rw [Subsingleton.elim i j]; simpa using continuous_id')
  have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
    refine MonoidHom.ext fun z => congrArg χ ?_
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩

theorem IsRec.recUnit {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) :
    RecUnit fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  intro χ c hu hc g α hα
  obtain ⟨hχ, e⟩ := cls_eq_ofChar χ c hc
  simp only [e, H.one, eig_lpOfChar, Multiset.mem_singleton] at hα
  rw [hα]
  exact hu _

end GlobalTheory.LocLanglands
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSquareMatrixSpanColumnsIntegral
section
open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem exists_span_fin_of_fg {L : Type} [Field L] (O : ValuationSubring L) (n : ℕ) (N : Submodule O (Fin n → L))
    (hN : N.FG) : ∃ c : Fin n → Fin n → L, N = Submodule.span O (Set.range c) := by
  classical
  have : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  have : Module.Flat O N :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let k := Module.finrank O N
  let B : Module.Basis (Fin k) O N := Module.finBasis O N
  have hli : LinearIndependent O (fun i => (B i : Fin n → L)) :=
    B.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hliL : LinearIndependent L (fun i => (B i : Fin n → L)) :=
    (LinearIndependent.iff_fractionRing O L).1 hli
  have hk : k ≤ n := by simpa using hliL.fintype_card_le_finrank
  refine ⟨fun j => if h : (j : ℕ) < k then (B ⟨j, h⟩ : Fin n → L) else 0, le_antisymm ?_ ?_⟩
  · have hsp : N = Submodule.span O (Set.range fun i => (B i : Fin n → L)) := by
      have h1 := congrArg (Submodule.map N.subtype) B.span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h1
      exact h1.symm
    refine hsp.le.trans (Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, lt_of_lt_of_le i.2 hk⟩, by simp⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    by_cases h : (j : ℕ) < k
    · simp [h]
    · simp [h]

theorem mem_span_cols_iff {L : Type} [Field L] (O : ValuationSubring L) {n : ℕ} {ι : Type} [Fintype ι]
    (M : Matrix (Fin n) ι L) (v : Fin n → L) :
    v ∈ Submodule.span O (Set.range fun j i => M i j) ↔ ∃ u : ι → L, (∀ i, u i ∈ O) ∧ v = M *ᵥ u := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => c j, fun j => (c j).2, ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun j => ⟨u j, hu j⟩, ?_⟩
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_square_span_cols : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin n) ι L), ∃ b : Matrix (Fin n) (Fin n) L, ∀ v : Fin n → L,
      (∃ u : ι → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = M *ᵥ u) ↔ ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = b *ᵥ t := by
  intro L _ _ n ι _ _ M
  let O : ValuationSubring L := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  obtain ⟨c, hc⟩ := exists_span_fin_of_fg O n (Submodule.span O (Set.range fun j i => M i j))
    (Submodule.fg_span (Set.finite_range _))
  refine ⟨Matrix.of fun i j => c j i, fun v => ?_⟩
  have h1 := mem_span_cols_iff O M v
  have h2 := mem_span_cols_iff O (Matrix.of fun i j => c j i) v
  rw [hc] at h1
  exact h1.symm.trans h2

end GlobalTheory.Hk3.HoweG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvector
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

namespace GlobalTheory.TorusEigenform

section General

variable {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] [AddCommGroup V] [Module ℂ V]

theorem exists_char_of_isIrreducible {σ : Representation ℂ G V} (hs : IsSmooth σ) (hi : σ.IsIrreducible) :
    ∃ μ : G →* ℂˣ, ∀ g w, σ g w = (μ g : ℂ) • w := by
  have := nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h : ∀ g, ∃ c : ℂ, ∀ w, σ g w = c • w := fun g =>
    LocGL.exists_eq_smul_of_isSmooth hs hi
      ⟨σ g, fun a => by rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, mul_comm]⟩
  choose c hc using h
  let m : G →* ℂ :=
    { toFun := c
      map_one' := smul_left_injective ℂ hv (by simp [← hc])
      map_mul' := fun a b => smul_left_injective ℂ hv (by
        show c (a * b) • v = (c a * c b) • v
        rw [← hc, map_mul, Module.End.mul_apply, hc b, hc a, smul_smul]) }
  exact ⟨m.toHomUnits, fun g w => hc g w⟩

theorem exists_eigenform {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {χ : G →* ℂˣ} (hχ : IsSmoothChar χ) {x : V} (hx : x ≠ 0)
    (hxH : ∀ t ∈ H, ρ t x = (χ t : ℂ) • x) :
    ∃ (μ : G →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ g v, l (ρ g v) = (μ g : ℂ) * l v) ∧ ∀ h ∈ H, μ h = χ h := by
  let ρ' := twist ρ χ⁻¹
  have hρ' : ∀ g v, ρ' g v = ((χ g)⁻¹ : ℂˣ) • ρ g v := fun _ _ => rfl
  have hc := LocGL.isCompl_fixed_twKer (isSmooth_twist hρ hχ.inv) hH
  let T : Subrepresentation ρ := ⟨twKer ρ' H 1, fun g v hv => by
    have h1 : ρ' g v ∈ twKer ρ' H 1 :=
      twKer_le_comap ρ' H g (by rw [Subgroup.normalizer_eq_top]; trivial) hv
    have h2 := (twKer ρ' H 1).smul_mem (χ g : ℂ) h1
    rwa [hρ', ← Units.smul_def, smul_inv_smul] at h2⟩
  have hT : T ≠ ⊤ := fun h => by
    have h1 : x ∈ T.toSubmodule := by rw [h]; trivial
    have h2 : x ∈ fixed ρ' H := fun t => by
      rw [hρ', hxH t t.2, ← Units.smul_def, inv_smul_smul]; simp
    exact hx ((Submodule.disjoint_def.1 hc.disjoint) x h2 h1)
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨M, hM, hTM⟩ := (eq_top_or_exists_le_coatom T).resolve_left hT
  have hi := isIrreducible_subQuot hM.covBy_top
  let p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hs : IsSmooth (subQuot ⊤ M) :=
    IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ
  obtain ⟨μ, hμ⟩ := exists_char_of_isIrreducible hs hi
  have hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule := fun g v => by
    have := hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)
    exact (Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype)
      (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this
  have hM' : M.toSubmodule < ⊤ := lt_top_iff_ne_top.2 fun h =>
    hM.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨l, hl0, hlM⟩ := Submodule.exists_le_ker_of_lt_top _ hM'
  have hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := fun g v => by
    have := hlM (hμM g v)
    rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  refine ⟨μ, l, hl0, hle, fun h hh => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hl0 (LinearMap.ext hn)
  have h1 : ρ' h v - v ∈ T.toSubmodule := Submodule.subset_span ⟨⟨h, hh⟩, v, by simp⟩
  have h2 := hlM (hTM h1)
  rw [LinearMap.mem_ker, map_sub, hρ', Units.smul_def, map_smul, hle, sub_eq_zero, smul_eq_mul,
    ← mul_assoc] at h2
  have h3 := mul_right_cancel₀ hv (h2.trans (one_mul _).symm)
  rw [← Units.val_mul, Units.val_eq_one, inv_mul_eq_one] at h3
  exact h3.symm

end General

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem secondCountableTopology_units : SecondCountableTopology kˣ := by
  have : SecondCountableTopology k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    letI : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    open scoped Valued in
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    infer_instance
  exact Units.isEmbedding_val₀.secondCountableTopology


variable {k} in
theorem isSmoothChar_torusChar {n : ℕ} {θ : Fin n → kˣ →* ℂˣ} (hθ : ∀ i, IsSmoothChar (θ i)) :
    IsSmoothChar (torusChar θ) :=
  Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) (by
    show IsOpen _
    rw [MonoidHom.ker_one]
    exact isOpen_univ) fun i _ => (hθ i).comp _ (continuous_apply i)

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Fin n → kˣ) V) (x : V) (θ : Fin n → kˣ →* ℂˣ), IsSmooth ρ → HasFiniteLength ρ → (∀ i, IsSmoothChar (θ i)) → x ≠ 0 → (∀ t ∈ torusO k (Fin n), ρ t x = (torusChar θ t : ℂ) • x) → ∃ (ψ : Fin n → kˣ →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ t y, l (ρ t y) = (torusChar ψ t : ℂ) * l y) ∧ ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u := by
  intro k _ _ _ _ n V _ _ ρ x θ hρ hl hθ hx hxH
  haveI := secondCountableTopology_units k
  obtain ⟨μ, l, hl0, hle, hμ⟩ := exists_eigenform hρ hl (SmGL.UnramFixed.isCompact_torusO k (Fin n))
    (isSmoothChar_torusChar hθ) hx hxH
  refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i), l, hl0, fun t y => ?_, fun i u hu => ?_⟩
  · rw [hle, torusChar_apply]
    conv_lhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  · have h := hμ (Pi.mulSingle i u) fun j => by
      by_cases h : j = i
      · subst h; simpa using hu
      · simp [Pi.mulSingle_eq_of_ne h]
    rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp), Pi.mulSingle_eq_same] at h
    exact h

end GlobalTheory.TorusEigenform
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassElementaryDivisorColumnsCongr
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem hform_smul_smul (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (s t : L) (u v : Fin n → L) :
    Formalism.UG.hform σ J (s • u) (t • v) = σ s * t * Formalism.UG.hform σ J u v := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mulVec_single_int {n : ℕ} (V : Matrix (Fin n) (Fin n) L) (hV : ∀ i j, V i j ∈ Formalism.UG.intL L) (i : Fin n) :
    ∀ r, (V *ᵥ Pi.single i (1 : L)) r ∈ Formalism.UG.intL L := by
  intro r
  have : (V *ᵥ Pi.single i (1 : L)) r = V r i := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [this]; exact hV r i

theorem single_eq_smul {n : ℕ} (i : Fin n) (c : L) : (Pi.single i c : Fin n → L) = c • Pi.single i (1 : L) := by
  ext r; by_cases h : r = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem gram_class_columns : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L)
    (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ), (∀ i j, V i j ∈ Formalism.UG.intL L) →
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
    ∀ i j : Fin n, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j))
      (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (y *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j))) -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (x *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j)))) := by
  intro L _ _ ϖ σ q hU n n' JT x y V a hV hiff hG i j
  have hϖv : Valued.v ϖ ≤ 1 := by
    rw [hU.2.2.2.1]; exact le_of_lt (by decide)
  have hϖ : ϖ ∈ Formalism.UG.intL L := hϖv
  set k := max (a i) (a j) with hk
  set c : L := ϖ ^ k with hc
  have hcI : c ∈ Formalism.UG.intL L := (Formalism.UG.intL L).pow_mem hϖ _

  have hcond : ∀ l, a l ≤ k → ∀ r, (x *ᵥ (c • (V *ᵥ Pi.single l (1 : L)))) r ∈ Formalism.UG.intL L := by
    intro l hl
    have hI : ∀ t, (Pi.single l c : Fin n → L) t ∈ Formalism.UG.intL L := by
      intro t; by_cases h : t = l
      · subst h; simpa using hcI
      · simp [Pi.single_apply, h, (Formalism.UG.intL L).zero_mem]
    have := (hiff (Pi.single l c) hI).mpr (by
      intro t; by_cases h : t = l
      · subst h
        refine ⟨ϖ ^ (k - a t), (Formalism.UG.intL L).pow_mem hϖ _, ?_⟩
        simp [hc, ← pow_add, Nat.add_sub_cancel' hl]
      · simpa [Pi.single_apply, h] using dvdPow_zero ϖ (a t))
    rwa [single_eq_smul, mulVec_smul] at this
  have hD := hG _ _ (mulVec_single_int V hV i) (mulVec_single_int V hV j) c hcI
    (hcond i (le_max_left _ _)) (hcond j (le_max_right _ _))
  refine ⟨_, hD, ?_⟩
  rw [single_eq_smul i, single_eq_smul j, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul,
    hform_smul_smul, hform_smul_smul, map_pow, hU.2.2.1, hc, ← mul_sub, ← mul_assoc, ← pow_add, ← pow_add,
    min_add_max]

end GlobalTheory.Hk3.IntWitt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRationalAdjointClosedOfWeakChar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3

theorem hecke_operators_rational_adjoint_closed_of_weak_char : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH) ∧ ∀ j t, (A3.A.fam.L j t).OkH := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC
  have h := GlobalTheory.SplitHeckeCore.hecke_okH_comm R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models
  exact ⟨fun t => (h.1 t).1, fun j t => (h.2 j t).1⟩

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormIntegralPreimageLattice
section
open Matrix

namespace GlobalTheory.Hk3.HoweG.GramA

variable {L : Type} [Field L]

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (a b : Fin n → L) :
    Formalism.UG.hform σ J a b = (fun i => σ (a i)) ⬝ᵥ (J *ᵥ b) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem map_mulVec_eq (σ : L →+* L) {n m : ℕ} (A : Matrix (Fin n) (Fin m) L) (w : Fin m → L) :
    (fun i => σ ((A *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* Formalism.UG.cT σ A := by
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Formalism.UG.cT, dotProduct, Matrix.mulVec, Matrix.vecMul, map_sum, mul_comm]

theorem dot_mem (O : Subring L) {n : ℕ} {a b : Fin n → L} (ha : ∀ i, a i ∈ O) (hb : ∀ i, b i ∈ O) : a ⬝ᵥ b ∈ O :=
  Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ha k) (hb k)

theorem mulVec_mem (O : Subring L) {n m : ℕ} {A : Matrix (Fin n) (Fin m) L} {b : Fin m → L}
    (hA : ∀ i j, A i j ∈ O) (hb : ∀ i, b i ∈ O) : ∀ i, (A *ᵥ b) i ∈ O :=
  fun i => dot_mem O (hA i) hb

theorem hform_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ (u u' : Fin n → L) (w w' : Fin n' → L), (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
      (∀ i, w i ∈ Formalism.UG.intL L) → (∀ i, u' i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u') i ∈ Formalism.UG.intL L) →
      (∀ i, w' i ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w)
        (u' + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') ∈ Formalism.UG.intL L := by
  intro L _ _ σ n n' JS JT hσ hv hJS hJT hS hT x hx u u' w w' hu hxu hw hu' hxu' hw'
  have hS' := HoweSwap.cT_herm hS
  have hT' := HoweSwap.cT_herm hT
  have hSi := HoweSwap.cT_inv_herm JS hS'
  have iS : ∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := (HoweSwap.glint_int hJS).1
  have iT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := (HoweSwap.glint_int hJT).1
  have hσO : ∀ z, z ∈ Formalism.UG.intL L → σ z ∈ Formalism.UG.intL L := by
    intro z hz
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at hz ⊢
    rw [hv]; exact hz
  have e1 : (JS : Matrix (Fin n) (Fin n) L) * adj σ JS JT x = Formalism.UG.cT σ x * (JT : Matrix (Fin n') (Fin n') L) := by
    unfold adj
    rw [Matrix.mul_assoc, HoweSwap.mul_inv_cl]
  have e2 : Formalism.UG.cT σ (adj σ JS JT x) * (JS : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n') (Fin n') L) * x := by
    unfold adj
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hT', hSi, HoweSwap.cT_cT hσ, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul,
      Matrix.mul_one]
  have e3 : x * adj σ JS JT x = (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *
      (JT : Matrix (Fin n') (Fin n') L) := by
    unfold adj Formalism.UG.cT
    simp only [Matrix.mul_assoc]
  have h1 : ∀ b : Fin n → L, Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + adj σ JS JT x *ᵥ w) b =
      (fun i => σ (u i)) ⬝ᵥ ((JS : Matrix (Fin n) (Fin n) L) *ᵥ b) +
        (fun i => σ (w i)) ⬝ᵥ ((JT : Matrix (Fin n') (Fin n') L) *ᵥ (x *ᵥ b)) := by
    intro b
    have : (fun i => σ ((u + adj σ JS JT x *ᵥ w) i)) = (fun i => σ (u i)) + fun i => σ ((adj σ JS JT x *ᵥ w) i) := by
      ext i; simp
    rw [hform_eq_dot, this, add_dotProduct, map_mulVec_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e2,
      Matrix.mulVec_mulVec]
  have h2 : (fun i => σ (u i)) ⬝ᵥ ((JS : Matrix (Fin n) (Fin n) L) *ᵥ (adj σ JS JT x *ᵥ w')) =
      (fun i => σ ((x *ᵥ u) i)) ⬝ᵥ ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w') := by
    rw [map_mulVec_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1]
  have h3 : x *ᵥ (adj σ JS JT x *ᵥ w') =
      (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *ᵥ
        ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w') := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e3]
  rw [h1, Matrix.mulVec_add, dotProduct_add, h2, Matrix.mulVec_add, h3]
  refine add_mem (add_mem ?_ ?_) ?_
  · exact dot_mem _ (fun i => hσO _ (hu i)) (mulVec_mem _ iS hu')
  · exact dot_mem _ (fun i => hσO _ (hxu i)) (mulVec_mem _ iT hw')
  · refine dot_mem _ (fun i => hσO _ (hw i)) (mulVec_mem _ iT fun i => ?_)
    exact add_mem (hxu' i) (mulVec_mem _ hx (mulVec_mem _ iT hw') i)

end GlobalTheory.Hk3.HoweG.GramA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConjStatement
section
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a) (S : π.V ≃ₗ[ℂ] π.V), (∀ o φ, S (π.op (invTOp o) φ) = π.op (conjOp o) (S φ)) → π.IsCsd := by
  first | exact @GlobalTheory.CsdFromConj.isCsd_of_invT_conj | exact GlobalTheory.CsdFromConj.isCsd_of_invT_conj | (intros; apply GlobalTheory.CsdFromConj.isCsd_of_invT_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharacterEigenProductStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_character_eigen_product : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp (h := h) l)).eig σ).prod = ((x.eig σ).prod) ^ l := by
  intro E Ω _ _ _ _ _ A w h x l σ
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpSp, WD.lpChar_mk, WD.eig_mk, WD.eig_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
      DetSp.prod_roots_charpoly, DetSp.prod_roots_charpoly, DetSp.det_map, DetSp.det_diagEnd,
      Finset.prod_zpow, ← Units.coe_prod, DetSp.prod_spEig, Units.val_one, one_zpow, one_pow, mul_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentSumTemperedStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_sum_tempered : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ Δ Δ' : Segment (w.adicCompletion E), (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ ((rc Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).eig φ, ‖α‖ = 1) → ¬ Δ.Precedes Δ' := by
  first | exact @GlobalTheory.UnitaryPrecedes.not_precedes_of_unitary | exact GlobalTheory.UnitaryPrecedes.not_precedes_of_unitary | (intros; apply GlobalTheory.UnitaryPrecedes.not_precedes_of_unitary <;> assumption)
end

