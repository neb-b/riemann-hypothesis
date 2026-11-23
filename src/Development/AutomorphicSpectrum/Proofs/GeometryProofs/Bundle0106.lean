module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0046
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0099
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MaximalTorusInFibre
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularSectionsOpenNeighbourhood
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_germ (W : X.Opens) (t : Γ(X, W)) (q : Cpt ξ) (hq : q.1 ∈ W) (hW : genPt ξ ∈ W) :
    genMap ξ q (X.presheaf.germ W q.1 hq t) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW t) := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hq q.2 t)

theorem regAt_near {p : Cpt ξ} {a : Ω} (h : a ∈ regAt ξ p) :
    ∃ W : X.Opens, p.1 ∈ W ∧ ∀ q : Cpt ξ, q.1 ∈ W → a ∈ regAt ξ q := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨W, hp, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf s
  have hW : genPt ξ ∈ W := p.2.mem_open W.isOpen hp
  refine ⟨W, hp, fun q hq => ⟨X.presheaf.germ W q.1 hq t, ?_⟩⟩
  rw [genMap_germ W t q hq hW, genMap_germ W t p hp hW]

theorem regAt_near_finset {p : Cpt ξ} (A : Finset Ω) (h : ∀ a ∈ A, a ∈ regAt ξ p) :
    ∃ W : X.Opens, p.1 ∈ W ∧ ∀ q : Cpt ξ, q.1 ∈ W → ∀ a ∈ A, a ∈ regAt ξ q := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, fun _ _ _ ha => absurd ha (Finset.notMem_empty _)⟩
  | insert a A _ ih =>
    obtain ⟨W, hp, hW⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    obtain ⟨W', hp', hW'⟩ := regAt_near (h a (Finset.mem_insert_self a A))
    refine ⟨W ⊓ W', ⟨hp, hp'⟩, fun q hq b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hW' q hq.2
    · exact hW q hq.1 b hb

theorem lie_near (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (g : ℕ) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (hξ : IsCptGen ξ) (hG : SmoothOfRelativeDimension g G.hom)
    (p : Cpt ξ) (n : ℕ) (S : Fin n → Li) (Φ : Fin n → Module.Dual Ω Li)
    (hS : ∀ j, S j ∈ M.lat p) (hΦ : ∀ j, ∀ e ∈ M.lat p, Φ j e ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
      (∀ j, S j ∈ M.lat q) ∧ ∀ j, ∀ e ∈ M.lat q, Φ j e ∈ regAt ξ q := by
  classical
  obtain ⟨U, hpU, b, -, hb⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.lieLat_isVB X G g Ω ξ Li M hξ hG).1 p (Set.mem_univ p)
  have hbp := (hb p (Set.mem_univ p) hpU).2
  have hc : ∀ j, ∃ c : Fin g → regAt ξ p, ∑ s, c s • b s = S j := fun j => by
    have := hS j
    rw [hbp] at this
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose c hc using hc
  have hΦb : ∀ j s, Φ j (b s) ∈ regAt ξ p := fun j s =>
    hΦ j _ (by rw [hbp]; exact Submodule.subset_span ⟨s, rfl⟩)
  obtain ⟨W, hpW, hW⟩ := regAt_near_finset (ξ := ξ) (p := p)
    (Finset.univ.image (fun js : Fin n × Fin g => (c js.1 js.2 : Ω)) ∪
      Finset.univ.image (fun js : Fin n × Fin g => Φ js.1 (b js.2))) (by
      intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · obtain ⟨js, -, rfl⟩ := Finset.mem_image.1 ha
        exact (c js.1 js.2).2
      · obtain ⟨js, -, rfl⟩ := Finset.mem_image.1 ha
        exact hΦb js.1 js.2)
  refine ⟨U ⊓ W, ⟨hpU, hpW⟩, fun q hq => ?_⟩
  have hbq := (hb q (Set.mem_univ q) hq.1).2
  have hcq : ∀ j s, (c j s : Ω) ∈ regAt ξ q := fun j s =>
    hW q hq.2 _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(j, s), Finset.mem_univ _, rfl⟩))
  have hΦq : ∀ j s, Φ j (b s) ∈ regAt ξ q := fun j s =>
    hW q hq.2 _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(j, s), Finset.mem_univ _, rfl⟩))
  refine ⟨fun j => ?_, fun j e he => ?_⟩
  · rw [hbq, ← hc j]
    refine Submodule.sum_mem _ fun s _ => ?_
    have : (c j s) • b s = (⟨c j s, hcq j s⟩ : regAt ξ q) • b s := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · rw [hbq] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact hΦq j s
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul r x _ hx =>
      have : Φ j (r • x) = (r : Ω) * Φ j x := by
        show Φ j ((r : Ω) • x) = _
        simp
      rw [this]
      exact mul_mem r.2 hx

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootFlatPushforwardGeoFun
section
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.RootSum

theorem mono_smooth {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (t : ℝ)
    (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (j : Fin d) : IsSmoothHerm (monoLines (M.line t) m d j) := by
  unfold monoLines
  split_ifs
  · rename_i h
    generalize (Finsupp.toMultiset m).toList.get ⟨j, h⟩ = o
    cases o with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  · unfold IsSmoothHerm
    simp only [trivLine]
    exact contDiffOn_const

theorem PP_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem)
    (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.PP II (monomial m 1) = limUnder (𝓝[>] 0) fun t => M.arMono II t m := by
  exact Module.Basis.constr_basis (basisMonomials (Option (Ψ × Fin N)) ℝ) ℝ _ m

theorem geoFun_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)
    (m : Option (Ψ × Fin N) →₀ ℕ) : M.geoFun (monomial m 1) = M.geoMono m := by
  exact Module.Basis.constr_basis (basisMonomials (Option (Ψ × Fin N)) ℝ) ℝ _ m

theorem toA_pk_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (τ : Ψ) (m : Ψ × Fin N →₀ ℕ) :
    toA (pk τ 1 * monomial m (1 : ℝ) : RP Ψ N) =
      ∑ i : Fin N, monomial ((m + Finsupp.single (τ, i) 1).mapDomain some) (1 : ℝ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [toA, pk, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_one, X, monomial_mul, rename_monomial, add_comm, mul_one]

theorem sum_arMono (hP : PtsIntegrableStatement) (hM : MetricLocalStatement) (hD : DegreeStatement)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ)
    (R : RootFlat M τ) (hII : IsIntersectionSystem II) (m : Ψ × Fin N →₀ ℕ) (hm : m.degree = dimFl Ψ N)
    (t : ℝ) (ht : 0 < t) :
    ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some) =
      R.ht * M.geoMono (m.mapDomain some) -
        ptsIntegral M.P (pot (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N))) (R.v t) / (M.δ : ℝ) := by
  have h1 := _root_.GlobalTheory.CompanionTheory.Ar.Flat.sum_roots_eq hP hM M.K M.ι M.Ω R.F M.y R.φ (II M.K M.ι) M.P (dimFl Ψ N)
    (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) R.A R.S (dimFl Ψ N + 1) N
    (fun i => M.x t (τ, i)) (R.v t) (hII M.K M.ι) M.arith R.overInt le_rfl M.arith
    (mono_smooth M t _ _) R.A_smooth (fun i => M.x_smooth t _) (R.v_inv t) (R.v_smooth t)
    (by simp only [M.x_deg]; exact R.deg) (R.prod t ht)
  rw [Finset.sum_congr rfl fun i _ => arMono_add_single Ψ N M II t m (τ, i) hII hm, ← Finset.sum_div, h1,
    ← geoMono_eq hD Ψ N M t m hm, RootFlat.ht]
  ring

theorem PP_mono (hP : PtsIntegrableStatement) (hM : MetricLocalStatement) (hD : DegreeStatement)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ)
    (R : RootFlat M τ) (hII : IsIntersectionSystem II) (hC : M.Converges II) (m : Ψ × Fin N →₀ ℕ)
    (hm : m.degree = dimFl Ψ N) :
    M.PP II (toA (pk τ 1 * monomial m 1)) = R.ht * M.geoFun (toA (monomial m 1)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [toA_pk_monomial, map_sum, toA, rename_monomial, geoFun_monomial]
  simp only [PP_monomial]
  have h1 : Tendsto (fun t => ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))
      (𝓝[>] 0) (𝓝 (∑ i : Fin N, limUnder (𝓝[>] 0) fun t =>
        M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))) :=
    tendsto_finsetSum _ fun i _ => tendsto_nhds_limUnder (hC _)
  have h2 : Tendsto (fun t => ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))
      (𝓝[>] 0) (𝓝 (R.ht * M.geoMono (m.mapDomain some) - 0 / (M.δ : ℝ))) := by
    refine (tendsto_const_nhds.sub ((R.small m hm).div_const _)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (sum_arMono hP hM hD M II τ R hII m hm t ht).symm
  rw [tendsto_nhds_unique h1 h2, zero_div, sub_zero]

end GlobalTheory.CompanionTheory.Ar.Flat.RootSum

open GlobalTheory.CompanionTheory.Ar.Flat.RootSum in
theorem GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq : PtsIntegrableStatement → MetricLocalStatement → DegreeStatement → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ) (R : RootFlat M τ) (Q : RP Ψ N), IsIntersectionSystem II → M.Converges II → Q.IsHomogeneous (dimFl Ψ N) → M.PP II (toA (pk τ 1 * Q)) = R.ht * M.geoFun (toA Q) := by
  intro hP hM hD Ψ _ _ N M II τ R Q hII hC hQ
  have hQ' : Q = ∑ m ∈ Q.support, Q.coeff m • monomial m (1 : ℝ) := by
    conv_lhs => rw [Q.as_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have hA : ∀ (c : ℝ) (F : RP Ψ N), toA (c • F) = c • toA F := fun c F => map_smul (rename some) c F
  have hS : ∀ (s : Finset (Ψ × Fin N →₀ ℕ)) (F : _ → RP Ψ N), toA (∑ m ∈ s, F m) = ∑ m ∈ s, toA (F m) :=
    fun s F => map_sum (rename some) F s
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hQ', Finset.mul_sum, hS, hS, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : m.degree = dimFl Ψ N := by
    rw [Finsupp.degree_eq_weight_one]
    exact hQ (mem_support_iff.mp hm)
  rw [mul_smul_comm, hA, hA, map_smul, map_smul, PP_mono hP hM hD M II τ R hII hC m hd, smul_eq_mul, smul_eq_mul]
  ring
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootHeightDifferenceBound
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.CloseHt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

section Places

variable {L : Type} [Field L] [NumberField L]

lemma log_sup_support {ι : Type} [Fintype ι] (x : ι → L) (hx : ∃ i, x i ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (⨆ i, v (x i))).Finite := by
  classical
  obtain ⟨i₀, hi₀⟩ := hx
  haveI : Nonempty ι := ⟨i₀⟩
  have hS : (⋃ i ∈ Finset.univ.filter (fun i => x i ≠ 0),
      Function.mulSupport fun v : FinitePlace L => v (x i)).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun i hi => ?_
    exact FinitePlace.hasFiniteMulSupport (by simpa using hi)
  refine hS.subset fun v hv => ?_
  by_contra hn
  apply hv
  have h1 : ∀ i, x i ≠ 0 → v (x i) = 1 := by
    intro i hi
    by_contra h
    exact hn (Set.mem_biUnion (by simpa using hi) h)
  have h2 : ∀ i, v (x i) ≤ 1 := by
    intro i
    by_cases hi : x i = 0
    · simp [hi]
    · exact (h1 i hi).le
  have h3 : (⨆ i, v (x i)) = 1 := by
    have hle : (⨆ i, v (x i)) ≤ 1 := ciSup_le h2
    have hge : (1 : ℝ) ≤ ⨆ i, v (x i) := by
      have hb : BddAbove (Set.range fun i => v (x i)) := (Set.finite_range _).bddAbove
      calc (1 : ℝ) = v (x i₀) := (h1 i₀ hi₀).symm
        _ ≤ _ := le_ciSup hb i₀
    exact le_antisymm hle hge
  simp [h3]

lemma block_support {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (a : K → ℝ)
    (x : ∀ k, ι k → L) (hx : ∀ k, ∃ i, x k i ≠ 0) :
    (Function.support fun v : FinitePlace L => ∑ k, a k * Real.log (⨆ i, v (x k i))).Finite := by
  refine (Set.finite_iUnion fun k => log_sup_support (x k) (hx k)).subset fun v hv => ?_
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact Set.mem_iUnion.2 ⟨k, right_ne_zero_of_mul hk⟩

lemma avg_mem (S : (L →+* ℂ) → ℝ) {lo hi : ℝ} (h : ∀ σ, S σ ∈ Set.Icc lo hi) :
    (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ, S σ ∈ Set.Icc lo hi := by
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hc : ∀ r : ℝ, ∑ _σ : L →+* ℂ, r = Module.finrank ℚ L * r := fun r => by
    simp [Finset.card_univ, Embeddings.card L ℂ]
  have h1 : Module.finrank ℚ L * lo ≤ ∑ σ, S σ := by
    rw [← hc]
    exact Finset.sum_le_sum fun σ _ => (h σ).1
  have h2 : ∑ σ, S σ ≤ Module.finrank ℚ L * hi := by
    rw [← hc]
    exact Finset.sum_le_sum fun σ _ => (h σ).2
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hd]
    linarith
  · rw [inv_mul_eq_div, div_le_iff₀ hd]
    linarith

end Places

section Join

variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)]

lemma ptHt_sub_join (a₁ : K₁ → ℝ) (a₂ : K₂ → ℝ) (φ₁ : ((Σ k, ι₁ k) → ℂ) → ℝ) (φ₂ : ((Σ k, ι₂ k) → ℂ) → ℝ)
    (L : Type) [Field L] [NumberField L] (z : (Σ k, joinIdx ι₁ ι₂ k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ptHt a₁ φ₁ L (fun p => z (joinInl ι₁ ι₂ p)) - ptHt a₂ φ₂ L (fun p => z (joinInr ι₁ ι₂ p)) =
      ptHt (Sum.elim a₁ (-a₂))
        (fun Z => φ₁ (fun p => Z (joinInl ι₁ ι₂ p)) - φ₂ (fun p => Z (joinInr ι₁ ι₂ p))) L z := by
  unfold ptHt
  rw [← mul_sub]
  congr 1
  have s₁ := block_support (L := L) (ι := ι₁) a₁ (fun k i => z (joinInl ι₁ ι₂ ⟨k, i⟩))
    (fun k => hz (Sum.inl k))
  have s₂ := block_support (L := L) (ι := ι₂) a₂ (fun k i => z (joinInr ι₁ ι₂ ⟨k, i⟩))
    (fun k => hz (Sum.inr k))
  have e : (∑ᶠ v : FinitePlace L, ∑ k, Sum.elim a₁ (-a₂) k * Real.log (⨆ i, v (z ⟨k, i⟩))) =
      (∑ᶠ v : FinitePlace L, ∑ k, a₁ k * Real.log (⨆ i, v (z (joinInl ι₁ ι₂ ⟨k, i⟩)))) -
        ∑ᶠ v : FinitePlace L, ∑ k, a₂ k * Real.log (⨆ i, v (z (joinInr ι₁ ι₂ ⟨k, i⟩))) := by
    rw [← finsum_sub_distrib s₁ s₂]
    refine finsum_congr fun v => ?_
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rfl
  rw [e]
  simp only [Finset.sum_sub_distrib]
  simp only [joinInl, joinInr]
  ring

end Join

section Embed

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {L : Type} [Field L]

lemma aeval_emb (σ : L →+* ℂ) (z : (Σ k, ι k) → L) (f : MRing ι) :
    aeval (fun p => σ (z p)) f = σ (aeval z f) :=
  (comp_aeval_apply (R := ℤ) (f := z) σ.toIntAlgHom f).symm

lemma ptsOver_emb (σ : L →+* ℂ) {P : Ideal (MRing ι)} {z : (Σ k, ι k) → L} (hz : z ∈ ptsOver L P) :
    (fun p => σ (z p)) ∈ ptsOver ℂ P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · rw [aeval_emb, hz.2 f hf, map_zero]

lemma hasVal_emb (σ : L →+* ℂ) {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} {z : (Σ k, ι k) → L} {w : L}
    (h : HasVal y a u z w) : HasVal y a u (fun p => σ (z p)) (σ w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, h0, h1⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, hy, ?_, ?_⟩
  · rw [aeval_emb]
    exact (map_ne_zero σ).2 h0
  · rw [aeval_emb, aeval_emb, h1, map_mul]

end Embed

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

lemma line_a (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) : (M.line t j).a = (M.line 1 j).a := by
  cases j with
  | none => rfl
  | some r => simp [RootModel.line, M.x_deg]

lemma coef_eq {M R : RootModel Ψ N} (h : M.kA = R.kA) (lam : Wt Ψ N) (s : ℝ) (j : Option (Ψ × Fin N)) :
    M.coef lam s j = R.coef lam s j := by
  cases j with
  | none => simp [RootModel.coef, h]
  | some r => rfl

lemma sum_abs_coef (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℝ) :
    ∑ j, |M.coef lam s j| ≤ l1 lam + |s| := by
  rw [Fintype.sum_option, add_comm]
  have h1 : |M.coef lam s none| ≤ |s| := by
    have hk : (1 : ℝ) ≤ M.kA := by exact_mod_cast M.kA_pos
    simp only [RootModel.coef]
    rw [abs_div, Nat.abs_cast]
    exact div_le_self (abs_nonneg s) hk
  have h2 : ∑ r : Ψ × Fin N, |M.coef lam s (some r)| = l1 lam := by
    simp [RootModel.coef, l1, Fintype.sum_prod_type]
  linarith

def lineDefect (M R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    ((Σ k, joinIdx M.ι R.ι k) → ℂ) → ℝ := fun Z =>
  Real.log ((M.line t j).h fun p => Z (joinInl M.ι R.ι p)) -
    Real.log ((R.line 1 j).h fun p => Z (joinInr M.ι R.ι p))

lemma lineHt_sub (M R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) (L : Type) [Field L] [NumberField L]
    (z : (Σ k, joinIdx M.ι R.ι k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    lineHt (M.line t j) L (fun p => z (joinInl M.ι R.ι p)) -
        lineHt (R.line 1 j) L (fun p => z (joinInr M.ι R.ι p)) =
      ptHt (fun k => (joinDeg M R j k : ℝ)) (lineDefect M R t j) L z := by
  unfold lineHt
  rw [ptHt_sub_join _ _ _ _ L z hz]
  have e : (Sum.elim (fun k => ((M.line t j).a k : ℝ)) (-fun k => ((R.line 1 j).a k : ℝ))) =
      fun k => (joinDeg M R j k : ℝ) := by
    funext k
    cases k with
    | inl k => simp [joinDeg, line_a M t j]
    | inr k => simp [joinDeg]
  rw [e]
  rfl

theorem close_ht (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω)
    (u : Option (Ψ × Fin N) → M.Ω) (c t s lo hi : ℝ) (lam : Wt Ψ N) (hC : Close M R i u c)
    (hA : ArchBetween M R i u t lam s lo hi) (L : Type) [Field L] [NumberField L]
    (z) (hz : z ∈ ptsOver L (mCoordIdeal (joinOf M R i))) :
    rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) - rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) ∈
      Set.Icc (lo - (l1 lam + |s|) * c) (hi + (l1 lam + |s|) * c) := by
  obtain ⟨harith, hbir, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main Ψ N M R i
  choose val hval0 hval using fun j => hC.unit j L z hz
  have hc : 0 ≤ c := by
    obtain ⟨-, q, m, hq, -, hlog, -, -⟩ := hC.vert none
    have h0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    exact (mul_nonneg_iff_of_pos_left hq').1 (h0.trans hlog)

  let E : Option (Ψ × Fin N) → ℝ := fun j => (Module.finrank ℚ L : ℝ)⁻¹ *
    ∑ σ : L →+* ℂ, (lineDefect M R t j (fun p => σ (z p)) - Real.log ‖σ (val j)‖)
  let D : Option (Ψ × Fin N) → ℝ := fun j => lineHt (M.line t j) L (fun p => z (joinInl M.ι R.ι p)) -
    lineHt (R.line 1 j) L (fun p => z (joinInr M.ι R.ι p))
  have hD : ∀ j, |D j - E j| ≤ c := by
    intro j
    have := _root_.GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound (M.K ⊕ R.K) (joinIdx M.ι R.ι) M.Ω (joinOf M R i) (dimFl Ψ N + 1) harith hbir
      (joinDeg M R j) (u j) c (hC.vert j) (lineDefect M R t j) L z hz (val j) (hval0 j) (hval j)
    simp only [D, E]
    rw [lineHt_sub M R t j L z hz.1]
    exact this
  have hE : ∑ j, M.coef lam s j * E j ∈ Set.Icc lo hi := by
    have e : ∑ j, M.coef lam s j * E j = (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ : L →+* ℂ, ∑ j, M.coef lam s j *
        (lineDefect M R t j (fun p => σ (z p)) - Real.log ‖σ (val j)‖) := by
      simp only [E]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      ring
    rw [e]
    refine avg_mem _ fun σ => ?_
    exact hA _ (ptsOver_emb σ hz) (fun j => σ (val j)) fun j => hasVal_emb σ (hval j)
  have hsplit : rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) -
      rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) =
      ∑ j, M.coef lam s j * E j + ∑ j, M.coef lam s j * (D j - E j) := by
    unfold rootHt
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← coef_eq hC.kA lam s j]
    simp only [D]
    ring
  have hb : |∑ j, M.coef lam s j * (D j - E j)| ≤ (l1 lam + |s|) * c := by
    calc |∑ j, M.coef lam s j * (D j - E j)| ≤ ∑ j, |M.coef lam s j * (D j - E j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |M.coef lam s j| * c := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hD j) (abs_nonneg _)
      _ = (∑ j, |M.coef lam s j|) * c := by rw [Finset.sum_mul]
      _ ≤ (l1 lam + |s|) * c := mul_le_mul_of_nonneg_right (sum_abs_coef M lam s) hc
  rw [hsplit]
  have := abs_le.1 hb
  exact ⟨by linarith [hE.1, this.1], by linarith [hE.2, this.2]⟩

end GlobalTheory.CompanionTheory.Ar.Ht.CloseHt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionRankBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.MaxTorus

theorem kernel_eq_of_rank_le : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (x : Sp k ⟶ S), (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G.left), IsGrpPullback Gk G x ψ → ∀ τ : TorusExtension Gk, (letI := τ.addCommGroup; Module.finrank ℤ τ.X ≤ Module.finrank ℤ X) → letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus S X, (t ≫ u).left = p.left ≫ ψ :=
  @PositivityTheory.Xgn.maximal_torus_in_fibre

end GlobalTheory.CompanionTheory.Ar.MaxTorus
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionSplitMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem torus_extension_generic : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 :=
  @PositivityTheory.Xgn.exists_split_torus_extension

end GlobalTheory.CompanionTheory.Ar
end

