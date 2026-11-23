module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0368
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QbKLeLocLev
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct Topology

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
attribute [local instance] rlt_top rlt_topRing

namespace GlobalTheory.Mem.Col2.TopCh

section Nhd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_nhds (P : HeightOneSpectrum (𝓞 E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ y in 𝓝 (0 : AfE F E), ∃ z ∈ P.adicCompletionIntegers E, adAt F P y = algebraMap E (P.adicCompletion E) c * z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
  have hb0 : algebraMap (𝓞 E) E b ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hb
  have ha0 : algebraMap (𝓞 E) E a ≠ 0 := fun h => hc (by rw [h, zero_div])
  set A : AfE F E := inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) with hA
  set B : AfE F E := inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a)⁻¹ with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← map_mul, mul_inv_cancel₀ ha0, map_one]
  have hop : IsOpen ((fun y : AfE F E => B * y) ⁻¹' (Formalism.L2.Herm.intAf F E : Set (AfE F E))) :=
    rlt_isOpen_intAf.preimage (continuous_const.mul continuous_id)
  have h0 : (0 : AfE F E) ∈ (fun y : AfE F E => B * y) ⁻¹' (Formalism.L2.Herm.intAf F E : Set (AfE F E)) := by
    simp
  filter_upwards [hop.mem_nhds h0] with y hy
  have hw : ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (afIso F E (B * y) Q) ≤ 1 := (mem_rInt_iff F E (B * y)).1 hy
  have hy' : y = A * (B * y) := by rw [← mul_assoc, hAB, one_mul]
  refine ⟨algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E b) * adAt F P (B * y), ?_, ?_⟩
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [map_mul]
    exact mul_le_one' (by rw [valued_algebraMap]; exact P.valuation_le_one b) (by rw [adAt_apply]; exact hw P)
  · have e : adAt F P y = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E a) * adAt F P (B * y) := by
      conv_lhs => rw [hy', map_mul, hA, adAt_inclE]
    rw [e, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hb0]

variable {n : ℕ}

theorem bc_adAt_sub (P : HeightOneSpectrum (𝓞 E)) (w : GL (Fin n) (AfE F E)) (i j : Fin n) :
    ((rhoP F P w : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j -
      (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j =
    adAt F P ((w : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  have e : ((rhoP F P w : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j =
      adAt F P ((w : Matrix (Fin n) (Fin n) (AfE F E)) i j) := rfl
  rw [e, map_sub, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem int_of_sub {P : HeightOneSpectrum (𝓞 E)} {A : Matrix (Fin n) (Fin n) (P.adicCompletion E)}
    (h : ∀ i j, A i j - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j ∈ P.adicCompletionIntegers E) : qbInt A := fun i j => by
  have := Subring.add_mem _ (h i j) (qbInt_one (v := P) (F := E) (n := n) i j)
  simpa using this

theorem eventually_localComponent_mem (P : HeightOneSpectrum (𝓞 E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, rhoP F P u ∈ qbK (algebraMap E (P.adicCompletion E) c) := by
  have hval : ∀ (c' : E), c' ≠ 0 → ∀ i j : Fin n, ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, ∃ z ∈ P.adicCompletionIntegers E,
      adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E (P.adicCompletion E) c' * z := by
    intro c' hc' i j
    have hcont : Continuous fun u : GL (Fin n) (AfE F E) =>
        (u : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j :=
      (Units.continuous_val.matrix_elem i j).sub continuous_const
    have ht := hcont.tendsto 1
    simp only [Units.val_one, sub_self] at ht
    exact ht.eventually (adAt_nhds P hc')
  have hinv : ∀ i j : Fin n, ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, ∃ z ∈ P.adicCompletionIntegers E,
      adAt F P (((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E (P.adicCompletion E) 1 * z := by
    intro i j
    have ht : Filter.Tendsto (fun u : GL (Fin n) (AfE F E) => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv (G := GL (Fin n) (AfE F E))).tendsto 1
    exact ht.eventually (hval 1 one_ne_zero i j)
  have h1 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hval c hc i j
  have h2 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hval 1 one_ne_zero i j
  have h3 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hinv i j
  filter_upwards [h1, h2, h3] with u a1 a2 a3
  refine ⟨int_of_sub fun i j => ?_, int_of_sub fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨z, hz, e⟩ := a2 i j
    rw [bc_adAt_sub, e, map_one, one_mul]
    exact hz
  · obtain ⟨z, hz, e⟩ := a3 i j
    rw [← map_inv, bc_adAt_sub, e, map_one, one_mul]
    exact hz
  · obtain ⟨z, hz, e⟩ := a1 i j
    exact ⟨z, hz, by rw [Matrix.sub_apply, bc_adAt_sub, e]⟩

theorem rhoT_nhds (P : HeightOneSpectrum (𝓞 E)) (t : GL (Fin n) (AfE F E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ x : GL (Fin n) (AfE F E) in 𝓝 1, rhoT F P t x ∈ qbK (algebraMap E (P.adicCompletion E) c) := by
  have hcont : Continuous fun x : GL (Fin n) (AfE F E) => t⁻¹ * x * t⁻¹⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have ht := hcont.tendsto 1
  simp only [mul_one, inv_inv, inv_mul_cancel] at ht
  exact ht.eventually (eventually_localComponent_mem P hc)

end Nhd

theorem qbK_le_locLev {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (Θ : LevI E K n P) (d : E) : qbK (algebraMap E (P.adicCompletion E) d) ≤ locLev P Θ d := fun k hk =>
  ⟨hk.1, hk.2.1, 1, Θ.H.one_mem, by simpa using hk⟩

theorem topU_open : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Q : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E), (∀ P, d P ≠ 0) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ U}) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ topU U t Θ d}) := by
  intro F E K _ _ _ _ _ _ _ σ n J Q U t Θ d hd hU
  have hW : ∀ P : Q, IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) |
      (x : GL (Fin n) (AfE F E)) ∈ (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)} := by
    intro P
    let W : Subgroup (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
      ((locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))
    have hn : (W : Set (UPts σ J (FiniteAdeleRing (𝓞 F) F))) ∈ 𝓝 (1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) := by
      have ht : Filter.Tendsto (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => (x : GL (Fin n) (AfE F E))) (𝓝 1) (𝓝 1) :=
        continuous_subtype_val.tendsto 1
      filter_upwards [ht.eventually (rhoT_nhds P.1 t (hd P))] with x hx
      exact qbK_le_locLev P.1 (Θ P) (d P) hx
    exact Subgroup.isOpen_of_mem_nhds W hn
  have e : {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL (Fin n) (AfE F E)) ∈ topU U t Θ d} =
      {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL (Fin n) (AfE F E)) ∈ U} ∩
        ⋂ P : Q, {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) |
          (x : GL (Fin n) (AfE F E)) ∈ (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)} := by
    ext x
    simp only [topU, Subgroup.mem_inf, Subgroup.mem_iInf, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact hU.inter (isOpen_iInter_of_finite hW)

end GlobalTheory.Mem.Col2.TopCh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitLatOfOneOne
section
open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat GlobalTheory.HermModel GlobalTheory.SplitGenus
open scoped nonZeroDivisors

namespace GlobalTheory.AnyLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {H : Host E}

theorem exists_isotropic (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) (D₀ : Datum H) (hp : D₀.p = 1) (hq : D₀.q = 1)
    (G : Matrix (Fin r) (Fin r) E) (φ₀ : D₀.La →ₗ[𝓞 E] (Fin r → E))
    (hM : Function.Injective φ₀ ∧ Submodule.span E (Set.range φ₀) = ⊤ ∧ (∀ a b, FD.cc (G a b) = G b a) ∧ G.det ≠ 0 ∧
      ∀ x y, ((D₀.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E ((H.rt : E) * FD.herm G (φ₀ x) (φ₀ y))) :
    ∃ z : Fin r → E, z ≠ 0 ∧ FD.herm G z z = 0 := by
  obtain ⟨D₁, p1, q1⟩ := h1
  let D₂ := DatumSum.sumDatum D₁ (CM.ConjDatum.conj D₁)
  have p2 : D₂.p = D₀.p := by
    change D₁.p + D₁.q = _
    omega
  have q2 : D₂.q = D₀.q := by
    change D₁.q + D₁.p = _
    omega
  obtain ⟨φ, inj, -, -, -, hEF⟩ := GlobalTheory.model_in_same_space
    (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt)
    GlobalTheory.QNorm.hasseNormSt E H D₀ D₂ _ (H.rt : E) G φ₀ p2 q2 (GlobalTheory.OneSpace.cc_rt H) hM
  have : Nontrivial D₁.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D₁.rank]; omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : D₁.La)
  let v : D₂.La := (x, x)
  refine ⟨φ v, fun h => hx (congrArg Prod.fst (inj (h.trans (map_zero φ).symm))), ?_⟩
  rw [← herm_zero_left G (φ v)]
  refine herm_eq_of_trace G (GlobalTheory.OneSpace.rt_ne H) fun s => ?_
  have e : D₂.EF (s • v) v = D₁.EF (s • x) x + D₁.EF (H.bar s • x) x :=
    DatumSum.sumForm_apply D₁.EF (CM.ConjDatum.conj D₁).EF (s • v) v
  have e2 : D₁.EF (s • x) x + D₁.EF (H.bar s • x) x = 0 := by
    have h := D₁.alt (x + H.bar s • x)
    simp only [map_add (f := _), LinearMap.add_apply, D₁.alt] at h
    rw [D₁.adj]
    linarith
  rw [← map_smul, ← hEF, e, e2, smul_zero, herm_zero_left]
  simp

theorem splitLat_of_one_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → D.p = 1 → D.q = 1 → SplitLat D := by
  intro E _ _ _ H D h1 hp hq
  obtain ⟨D₀, ep, eq, Lp, Lm, htop, ho, rp, rm, sp, sm⟩ := _root_.GlobalTheory.CompRat.exists_splitLat_of_signature E H D.p D.q h1
  have := D.fin
  have := D₀.fin
  have hξ := GlobalTheory.OneSpace.cc_rt H
  have hξ0 := GlobalTheory.OneSpace.rt_ne H
  obtain ⟨G, φ₀, hM₀⟩ := GlobalTheory.exists_herm_coord_of_datum E H D₀ (H.rt : E) hξ hξ0 (D.p + D.q) (by rw [ep, eq])
  obtain ⟨φ, hM⟩ := GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt)
    GlobalTheory.QNorm.hasseNormSt E H D₀ D _ (H.rt : E) G φ₀ ep.symm eq.symm hξ hM₀
  have hz := exists_isotropic h1 D₀ (ep.trans hp) (eq.trans hq) G φ₀ hM₀
  obtain ⟨-, hfg, -, hdual⟩ := rank_integral_selfDual E H D _ _ G φ hξ hM
  obtain ⟨inj₀, span₀, hG, hdet, hEF₀⟩ := hM₀
  obtain ⟨inj, span, -, -, hEF⟩ := hM
  have hc : IsCompl Lp Lm := by
    refine ⟨Submodule.disjoint_def.2 fun a ha hb => ?_, codisjoint_iff.2 htop⟩
    by_contra h0
    exact lt_asymm (sp a ha h0) (sm a hb h0)
  obtain ⟨π, π1, π2, π3, π4, π5⟩ := exists_projector D₀ G φ₀ inj₀ span₀ hG hEF₀ Lp Lm hc ho
  have hh : GlobalTheory.UTrans.IsHerm (IsCMField.complexConj E : E →+* E) G := by
    refine ⟨fun a => IsCMField.complexConj_apply_apply E a, ⟨(H.rt : E), fun h => hξ0 ?_⟩, hG, hdet⟩
    have h2 : (H.rt : E) = -(H.rt : E) := h.symm.trans hξ
    linear_combination (1 / 2 : E) * h2
  have : Nontrivial Lp := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by omega)
  obtain ⟨⟨a, ha⟩, ha0⟩ := exists_ne (0 : Lp)
  have hxx : FD.herm G (φ₀ a) (φ₀ a) ≠ 0 := by
    intro h
    have h5 := sp a ha fun h => ha0 (Subtype.ext h)
    have h6 := hEF₀ (H.rt • a) a
    rw [map_smul φ₀, show H.rt • φ₀ a = (H.rt : E) • φ₀ a from rfl, herm_smul_left, h, mul_zero, mul_zero,
      map_zero] at h6
    have h7 : D₀.EF (H.rt • a) a = 0 := by exact_mod_cast h6
    rw [h7] at h5
    simp at h5
  obtain ⟨b₁, hb₁, m₁⟩ := GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ φ₀ span₀
  obtain ⟨b₂, hb₂, m₂⟩ := GlobalTheory.SelfDualIsom.exists_nat_smul_mem φ₀ φ span
  obtain ⟨k, f, hk, hf⟩ := GlobalTheory.T.exists_coprime_scaled_isometry_same_signature E H D D₀ ep eq (2 * b₁ * b₂) (by positivity)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hk
    rw [mul_assoc] at hk
    omega
  have hkE : (k : E) ≠ 0 := by exact_mod_cast hk0
  have hkQ : (k : ℚ) ^ 2 ≠ 0 := by positivity
  obtain ⟨A, hA⟩ := exists_matrix φ (φ₀ ∘ₗ f) inj span
  have hA' : ∀ x, (k : E) • (((k : E)⁻¹ • A) *ᵥ φ x) = φ₀ (f x) := fun x => by
    rw [smul_mulVec, smul_smul, mul_inv_cancel₀ hkE, one_smul]
    exact hA x
  generalize (k : E)⁻¹ • A = γ₀ at hA'
  have hU₀ : ∀ x y, FD.herm G (γ₀ *ᵥ x) (γ₀ *ᵥ y) = FD.herm G x y := fun x y => by
    have := herm_ext G γ₀ γ₀ 1 1 span (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [one_mulVec, one_mulVec]
      refine herm_eq_of_trace G hξ0 fun s => ?_
      rw [show s • γ₀ *ᵥ φ x = (s : E) • γ₀ *ᵥ φ x from rfl, ← mulVec_smul,
        show (s : E) • φ x = s • φ x from rfl, ← map_smul]
      apply mul_left_cancel₀ hkQ
      rw [← trace_nsmul, hA', hA', ← hEF₀, ← hEF, hf]
      push_cast
      rfl) x y
    rwa [one_mulVec, one_mulVec] at this
  have hd₀ := isUnit_det hdet hU₀
  obtain ⟨γ, hU, hγ⟩ := _root_.GlobalTheory.UTrans.exists_isU_conj_mem (maximalRealSubfield E) E (IsCMField.complexConj E) _ G
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hh hz (LinearMap.range φ) (LinearMap.range φ₀) hfg span
    π γ₀ (φ₀ a) (2 * b₁ * b₂) k π1 π2 ((π4 a).2 ha) hxx (by rintro _ ⟨y, rfl⟩; exact π3 y) (by positivity)
    (by
      rintro _ ⟨x, rfl⟩
      rw [mul_right_comm, mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₁]
      exact nsmul_mem (m₁ x) _)
    (by
      rintro _ ⟨x, rfl⟩
      rw [mul_smul, ← Nat.cast_smul_eq_nsmul (𝓞 E) b₂]
      exact nsmul_mem (m₂ x) _)
    hU₀ hk
    (by
      rintro _ ⟨x, rfl⟩
      rw [← Nat.cast_smul_eq_nsmul E, hA']
      exact ⟨_, rfl⟩)
    (by
      rintro _ ⟨y, rfl⟩
      refine (hdual _).1 fun x => ⟨D₀.EF y (f x), ?_⟩
      rw [hEF₀, ← hA', ← Nat.cast_smul_eq_nsmul E, herm_smul_left, herm_smul_right, ← hU₀ (γ₀⁻¹ *ᵥ φ₀ y),
        mulVec_mulVec, mul_nonsing_inv _ hd₀, one_mulVec, show FD.cc (k : E) = k by simp [FD.cc], mul_comm (k : E)])
  have hU' : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y := hU
  have hd := isUnit_det hdet hU'
  obtain ⟨N, g, hN, hg⟩ := exists_scaled_map ((Matrix.toLin' γ).restrictScalars (𝓞 E) ∘ₗ φ) φ₀ inj₀ span₀
  have hg' : ∀ x, φ₀ (g x) = (N : E) • γ *ᵥ φ x := hg
  have hE : ∀ x y, D₀.EF (g x) (g y) = (N : ℤ) ^ 2 * D.EF x y := fun x y => by
    have := hEF₀ (g x) (g y)
    rw [hg', hg', trace_nsmul, hU', ← hEF] at this
    exact_mod_cast this
  refine split_of_scaled D D₀ ep eq Lp Lm ho rp rm sp sm N hN g ?_ hE fun x => ?_
  · refine (injective_iff_map_eq_zero g).2 fun x hx => D.unimod.1 ?_
    ext y
    have := hE x y
    rw [hx, map_zero, LinearMap.zero_apply] at this
    rw [map_zero, LinearMap.zero_apply]
    exact (mul_eq_zero.1 this.symm).resolve_left (by positivity)
  · obtain ⟨c, hc⟩ := hγ _ ⟨x, rfl⟩
    have e : γ *ᵥ φ c = π *ᵥ (γ *ᵥ φ x) := by
      rw [hc, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd,
        Matrix.one_mul]
    have e2 : π *ᵥ (γ *ᵥ φ c) = γ *ᵥ φ c := by rw [e, mulVec_mulVec, π1]
    refine ⟨c, (π4 _).1 ?_, π5 _ ?_⟩
    · rw [hg', mulVec_smul, e2]
    · rw [hg', mulVec_smul, map_sub, mulVec_sub, mulVec_sub, e2, e, sub_self, smul_zero]

end GlobalTheory.AnyLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabIffMemConj
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

theorem stab_iff_mem_conj : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (U : Subgroup (GL (Fin n) (AfE F E))) (k' y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), (∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * k') p → IsPtOf hc (g * x * k') p' → (x ∈ U ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p')) → IsPtOf hc (y * k') p → ∀ γ : UF E n, (∃ (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p) ↔ ratAd F γ ∈ U.map (MulAut.conj y).toMonoidHom := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ U k' y p hlev hp γ
  have hγ : IsPtOf hc (ratAd F γ * (y * k')) (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
    first | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q γ (y * k') p hp | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd (hc := hc) γ hp | (apply GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd <;> assumption)
  have hx : IsPtOf hc (y * (y⁻¹ * ratAd F γ * y) * k') (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
    have : y * (y⁻¹ * ratAd F γ * y) * k' = ratAd F γ * (y * k') := by group
    rw [this]; exact hγ
  have key := hlev y (y⁻¹ * ratAd F γ * y) p _ hp hx
  have hmem : ratAd F γ ∈ U.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * ratAd F γ * y ∈ U := by
    constructor
    · rintro ⟨u, hu, he⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
      rw [← he]; simpa [mul_assoc] using hu
    · intro hu
      refine ⟨_, hu, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rw [hmem, key]
  constructor
  · rintro ⟨h, θ, he⟩
    refine ⟨h⁻¹, θ⁻¹, ?_⟩
    have e1 : ((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) = ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * (γ, h.1, θ.1) := by
      ext <;> simp
    rw [e1, mul_smul, he]
  · rintro ⟨h, θ, he⟩
    refine ⟨h⁻¹, θ⁻¹, ?_⟩
    have : ((γ, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) = ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * (γ, 1, 1) := by
      ext <;> simp
    rw [this, mul_smul, ← he, ← mul_smul]
    have : ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * (1, h.1, θ.1) = 1 := by
      ext <;> simp
    rw [this, one_smul]

end GlobalTheory.Mem.Col2.TopCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameSplitPlaceEntriesOffPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLevelSplit

theorem lemB_pf : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : GA D V), L.Pg ⊆ T → L.Q ⊆ T → x ∈ GfC V → finE V x ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T → x ∈ levS V β L ∧ levChi V β L x = 1 := by
  intro D V β L T x hg hq hx hK
  have h3 : ∀ PP ∈ T, Formalism.L2.DIV.redFn β PP (finE V x) = 1 := by
    have h1 : finE V x ∈ ⨅ PP ∈ T, Formalism.L2.DIV.princAt β PP := hK.2
    exact fun PP hP => (Formalism.L2.DIV.mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  refine ⟨⟨hx, Formalism.L2.DIV.Kg_le_lev hg hq hK⟩, ?_⟩
  have hr : Formalism.L2.DIV.rTup β L (finE V x) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn β PP.1 (finE V x)) = 1
    rw [h3 PP.1 (hg PP.2)]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi Formalism.L2.DIV.levFn
  rw [hr, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · rfl
  · intro PP hP
    rw [h3 PP (hq hP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h3 PP (hg hP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

theorem int_of_lt {D : D7} {n : ℕ} (y : Matrix (Fin n) (Fin n) (EAf D))
    (h : ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin n), Valued.v (GlobalTheory.StdFrames.cpt Q (y a b - (1 : Matrix (Fin n) (Fin n) (EAf D)) a b)) < 1)
    (a b : Fin n) : y a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h1 : (1 : Matrix (Fin n) (Fin n) (EAf D)) a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have h2 : y a b - (1 : Matrix (Fin n) (Fin n) (EAf D)) a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    (GlobalTheory.AdIsom.mem_OA _).2 fun Q => le_of_lt (h Q a b)
  have := add_mem h2 h1
  rwa [sub_add_cancel] at this

set_option maxHeartbeats 2000000 in
theorem glInt_of_int {D : D7} {n : ℕ} (y : GL (Fin n) (EAf D))
    (i1 : ∀ a b, y.val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (i2 : ∀ a b, (y⁻¹).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ z : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.intGL D.host.F D.host.E n z = y ∧
      ∀ a b, ((z.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = y.val a b := by
  let φ : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) →+* Matrix (Fin n) (Fin n) (EAf D) :=
    RingHom.mapMatrix (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
  have inj : Function.Injective φ := fun M N h => Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
  let zM : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) := Matrix.of fun a b => ⟨_, i1 a b⟩
  let zI : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) := Matrix.of fun a b => ⟨_, i2 a b⟩
  have e1 : φ zM = y.val := by ext a b; rfl
  have e2 : φ zI = (y⁻¹).val := by ext a b; rfl
  have m1 : zM * zI = 1 := inj (show φ (zM * zI) = φ 1 by rw [map_mul, map_one, e1, e2, Units.mul_inv])
  have m2 : zI * zM = 1 := inj (show φ (zI * zM) = φ 1 by rw [map_mul, map_one, e1, e2, Units.inv_mul])
  exact ⟨⟨zM, zI, m1, m2⟩, Units.ext e1, fun a b => rfl⟩

set_option maxHeartbeats 800000 in
theorem kg_of_cpt : ∀ (D : D7) (V : HSp D) (β x : GL (Fin V.rank) (EAf D)) (T : Finset (Formalism.L2.DIV.Pl D.host.E)), x ∈ Formalism.L2.DIV.UA D.sp.cm V.gram → (∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * x * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → (∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * x⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → x ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T := by
  intro D V β x T hU h1 h2
  have hyi : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  have i1 := int_of_lt (β⁻¹ * x * β).val h1
  have i2 := int_of_lt ((β⁻¹ * x * β)⁻¹).val (by rw [hyi]; exact h2)
  obtain ⟨z, hz0, hzv⟩ := glInt_of_int (β⁻¹ * x * β) i1 i2
  have hz : Formalism.L2.DIV.frGL β z = x := by
    show β * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank z * β⁻¹ = x
    rw [hz0]; group
  have hS : x ∈ Formalism.L2.DIV.St β := ⟨z, hz⟩
  have hred : ∀ PP, Formalism.L2.DIV.redFn β PP x = 1 := by
    intro PP
    rw [← hz, Formalism.L2.DIV.redFn_frGL]
    apply Units.ext
    ext a b
    show Formalism.L2.DIV.resS D.host.F PP (z.val a b) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP PP)) a b
    have h0 : Formalism.L2.DIV.resS D.host.F PP (z.val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b) = 0 := by
      rw [GlobalTheory.AdIsom.resS_eq_zero_iff_cpt]
      have e3 : ((z.val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
          (β⁻¹ * x * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b := by
        rw [← hzv a b, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
      rw [e3]; exact h1 PP a b
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  exact ⟨⟨hU, hS⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun _ => Formalism.L2.DIV.mem_princAt.2 ⟨hS, hred PP⟩⟩

theorem trivOutside_inv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside T x) : TrivOutside T x⁻¹ := fun v hv => by
  have h1 : (((x⁻¹ : Formalism.AUTREP.GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
  have h2 := congrArg (fun M => Matrix.map M (compAt L v)) h1
  simp only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  exact h2

theorem lemA_pf (hC2 : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ T : Finset (Formalism.L2.DIV.Pl D.host.E), finE V (P.ψ κ) ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T := by
  intro D V n hF P β Λ N hS hβ s
  obtain ⟨h, hh⟩ := hC2 D V n hF P β Λ N hS hβ s
  refine ⟨h, fun κ hκ hk T => ?_⟩
  have hk' : h⁻¹ * s.loc n κ⁻¹ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) := by
    have := Subgroup.inv_mem _ hk
    rwa [show (h⁻¹ * s.loc n κ * h)⁻¹ = h⁻¹ * (s.loc n κ)⁻¹ * h by group, ← map_inv] at this
  have e : finE V (P.ψ κ⁻¹) = (finE V (P.ψ κ))⁻¹ := by rw [map_inv, map_inv]
  refine kg_of_cpt D V β (finE V (P.ψ κ)) T (GlobalTheory.LevSplit.finE_mem_UA V _) (hh κ hκ hk) ?_
  have := hh κ⁻¹ (trivOutside_inv hκ) hk'
  rwa [e] at this

theorem stdFrame_splitPlace_entries_off_place (hA : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), TrivOutside {s.v} κ → ∀ (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal → ∀ (a b : Fin V.rank), GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b) = GlobalTheory.StdFrames.cpt Q ((1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) (hC : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) (hDd : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) (hE : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (s : SplitPlace D.host.E) (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal → Q = s.w ∨ Q = GlobalTheory.IdemSupport.cP s.w) : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  intro D V n hF P β Λ N hS hβ s
  obtain ⟨h, hh⟩ := hDd D V n hF P β hS s
  refine ⟨h, fun κ hκ hk Q a b => ?_⟩
  by_cases hQ : Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal
  · rcases hE D hF s Q hQ with rfl | rfl
    · exact hh κ hκ hk a b
    · have hk' : h⁻¹ * s.loc n κ⁻¹ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) := by
        have := Subgroup.inv_mem _ hk
        rwa [show (h⁻¹ * s.loc n κ * h)⁻¹ = h⁻¹ * (s.loc n κ)⁻¹ * h by group, ← map_inv] at this
      refine hC D V β Λ N hβ (P.ψ κ) s.w (fun a b => ?_) a b
      have := hh κ⁻¹ (trivOutside_inv hκ) hk' a b
      rwa [map_inv, map_inv] at this
  · rw [map_sub, hA D V n hF P β hS s κ hκ Q hQ a b, sub_self, map_zero]
    exact zero_lt_one

end GlobalTheory.RowLevelSplit
end
end

