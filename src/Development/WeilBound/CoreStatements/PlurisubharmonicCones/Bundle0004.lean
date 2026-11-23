module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeDetIdeal
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FiniteOfTorsion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemEig
section
noncomputable section

namespace LevelTowerAlt

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
open scoped Pointwise

set_option linter.unusedSectionVars false

section Free

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
theorem pow_mul_detIdeal_le {n : ℕ} (𝔞 : Ideal (𝓞 K)) (E : Submodule (𝓞 K) (Fin n → 𝓞 K)) :
    𝔞 ^ n * detIdeal E ≤ detIdeal (𝔞 • E) := by
  have h1 : 𝔞 ^ n = Ideal.span (∏ _i : Fin n, (𝔞 : Set (𝓞 K))) := by
    rw [← Ideal.prod_span]
    simp
  rw [h1, detIdeal, Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨a, ha, d, ⟨v, hv, rfl⟩, rfl⟩
  obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_prod _ _).1 ha
  have h := det_mem_detIdeal (𝔞 • E) (fun i => g i • v i) fun i => Submodule.smul_mem_smul (hg i) (hv i)
  have e : (Matrix.of fun i => g i • v i).det = (∏ i, g i) * (Matrix.of v).det :=
    Matrix.det_mul_column g (Matrix.of v)
  rw [e] at h
  exact h

theorem relIndex_smul_free {n : ℕ} (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) (E : Submodule (𝓞 K) (Fin n → 𝓞 K))
    (d : 𝓞 K) (hd : d ≠ 0) (hE : ∀ x, d • x ∈ E) :
    (𝔞 • E).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 ∧
      (𝔞 • E).toAddSubgroup.relIndex E.toAddSubgroup ≤ Ideal.absNorm 𝔞 ^ n := by
  classical
  have hD : detIdeal E ≠ ⊥ := by
    have h := det_mem_detIdeal E (fun i => d • Pi.single i 1) fun i => hE _
    have e : (Matrix.of fun i : Fin n => d • (Pi.single i 1 : Fin n → 𝓞 K)) = d • (1 : Matrix (Fin n) (Fin n) (𝓞 K)) := by
      ext i j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [e, Matrix.det_smul, Matrix.det_one, mul_one] at h
    intro h0
    rw [h0, Ideal.mem_bot] at h
    exact pow_ne_zero _ hd h
  have h1 : E.toAddSubgroup.index = Ideal.absNorm (detIdeal E) := card_quotient_eq_absNorm_detIdeal n E
  have h2 : (𝔞 • E).toAddSubgroup.index = Ideal.absNorm (detIdeal (𝔞 • E)) :=
    card_quotient_eq_absNorm_detIdeal n (𝔞 • E)
  have h3 := AddSubgroup.relIndex_mul_index (H := (𝔞 • E).toAddSubgroup) (K := E.toAddSubgroup)
    (fun x hx => (Submodule.smul_le_right (I := 𝔞) (N := E)) hx)
  have h4 := Ideal.absNorm_dvd_absNorm_of_le (pow_mul_detIdeal_le 𝔞 E)
  rw [map_mul, map_pow, ← h2, ← h3, h1] at h4
  have hN : Ideal.absNorm (detIdeal E) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hD
  have hA : Ideal.absNorm 𝔞 ^ n ≠ 0 := pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 h𝔞)
  have h5 := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hN) h4
  exact ⟨ne_zero_of_dvd_ne_zero hA h5, Nat.le_of_dvd (Nat.pos_of_ne_zero hA) h5⟩

end Free

variable {L V : Type} [Field L] [NumberField L] [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
  [IsScalarTower (𝓞 L) L V]

def Sub (X Y : Submodule (𝓞 L) V) : Prop := ∃ c : 𝓞 L, c ≠ 0 ∧ ∀ x ∈ X, c • x ∈ Y

omit [Module L V] [IsScalarTower (𝓞 L) L V] in
theorem Sub.trans {X Y Z : Submodule (𝓞 L) V} (h : Sub X Y) (h' : Sub Y Z) : Sub X Z := by
  obtain ⟨c, hc, h⟩ := h
  obtain ⟨d, hd, h'⟩ := h'
  exact ⟨d * c, mul_ne_zero hd hc, fun x hx => by rw [mul_smul]; exact h' _ (h x hx)⟩

omit [Module L V] [IsScalarTower (𝓞 L) L V] in
theorem Sub.of_le {X Y : Submodule (𝓞 L) V} (h : X ≤ Y) : Sub X Y :=
  ⟨1, one_ne_zero, fun x hx => by rw [one_smul]; exact h hx⟩

omit [Module L V] [IsScalarTower (𝓞 L) L V] [NumberField L] in
theorem Sub.of_smul_le {X Y : Submodule (𝓞 L) V} {𝔞 : Ideal (𝓞 L)} (h𝔞 : 𝔞 ≠ ⊥) (h : 𝔞 • X ≤ Y) : Sub X Y := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  exact ⟨a, ha0, fun x hx => h (Submodule.smul_mem_smul ha hx)⟩

theorem exists_smul_mem_of_mem_span (Y : Submodule (𝓞 L) V) {S : Set V} (hS : ∀ x ∈ S, x ∈ Y) {p : V}
    (hp : p ∈ Submodule.span L S) : ∃ b : 𝓞 L, b ≠ 0 ∧ b • p ∈ Y :=
  _root_.UpperTheory.Reformulated.B.Qo3.exists_smul_mem_of_mem_span Y hS hp

omit [Module L V] [IsScalarTower (𝓞 L) L V] in
theorem Sub.of_fg {X Y : Submodule (𝓞 L) V} (hX : X.FG) (h : ∀ x ∈ X, ∃ b : 𝓞 L, b ≠ 0 ∧ b • x ∈ Y) : Sub X Y := by
  classical
  obtain ⟨S, rfl⟩ := hX
  have h' : ∀ x : S, ∃ b : 𝓞 L, b ≠ 0 ∧ b • (x : V) ∈ Y := fun x => h x (Submodule.subset_span x.2)
  choose g hg0 hg using h'
  refine ⟨∏ x, g x, Finset.prod_ne_zero_iff.2 fun x _ => hg0 x, fun y hy => ?_⟩
  have hle : Submodule.span (𝓞 L) (S : Set V) ≤ Y.comap ((∏ x, g x) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro x hx
    change (∏ x, g x) • x ∈ Y
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : S)), mul_smul]
    exact Y.smul_mem _ (hg ⟨x, hx⟩)
  exact hle hy

theorem smul_injective {c : 𝓞 L} (hc : c ≠ 0) : Function.Injective fun x : V => c • x := by
  intro x y h
  have hL : algebraMap (𝓞 L) L c ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)]
    exact hc
  simp only [← algebraMap_smul L c] at h
  exact smul_right_injective V hL h

theorem relIndex_smul {n : ℕ} {b : Fin n → V} (hb : LinearIndependent L b) (𝔞 : Ideal (𝓞 L)) (h𝔞 : 𝔞 ≠ ⊥)
    {M : Submodule (𝓞 L) V} (h1 : Sub M (Submodule.span (𝓞 L) (Set.range b)))
    (h2 : Sub (Submodule.span (𝓞 L) (Set.range b)) M) :
    (𝔞 • M).toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 ∧
      (𝔞 • M).toAddSubgroup.relIndex M.toAddSubgroup ≤ Ideal.absNorm 𝔞 ^ n := by
  obtain ⟨c, hc, h1⟩ := h1
  obtain ⟨d, hd, h2⟩ := h2
  have hb' : LinearIndependent (𝓞 L) b := hb.restrict_scalars' (𝓞 L)
  set θ : (Fin n → 𝓞 L) →ₗ[𝓞 L] V := Fintype.linearCombination (𝓞 L) b with hθ
  have hθi : Function.Injective θ := hb'.fintypeLinearCombination_injective
  have hθr : LinearMap.range θ = Submodule.span (𝓞 L) (Set.range b) := Fintype.range_linearCombination _ _
  set μ : V →ₗ[𝓞 L] V := c • LinearMap.id with hμ
  have hμi : Function.Injective μ := smul_injective (L := L) hc
  set E := (M.map μ).comap θ with hE
  have hmap : E.map θ = M.map μ := by
    rw [hE, Submodule.map_comap_eq, hθr, inf_eq_right]
    rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  have hmap2 : (𝔞 • E).map θ = (𝔞 • M).map μ := by
    rw [Submodule.map_smul'', Submodule.map_smul'', hmap]
  have hEd : ∀ x, (c * d) • x ∈ E := by
    intro x
    refine ⟨d • θ x, h2 _ (hθr ▸ ⟨x, rfl⟩), ?_⟩
    rw [map_smul θ, mul_smul]
    rfl
  have h := relIndex_smul_free 𝔞 h𝔞 E (c * d) (mul_ne_zero hc hd) hEd
  have e1 := AddSubgroup.relIndex_map_map_of_injective (f := θ.toAddMonoidHom) (𝔞 • E).toAddSubgroup
    E.toAddSubgroup hθi
  have e2 := AddSubgroup.relIndex_map_map_of_injective (f := μ.toAddMonoidHom) (𝔞 • M).toAddSubgroup
    M.toAddSubgroup hμi
  have e3 : ((𝔞 • E).map θ).toAddSubgroup.relIndex (E.map θ).toAddSubgroup =
      ((𝔞 • M).map μ).toAddSubgroup.relIndex (M.map μ).toAddSubgroup := by rw [hmap, hmap2]
  have e4 : (𝔞 • E).toAddSubgroup.relIndex E.toAddSubgroup =
      (𝔞 • M).toAddSubgroup.relIndex M.toAddSubgroup := e1.symm.trans (e3.trans e2)
  rwa [e4] at h

theorem relIndex_ne_zero {n : ℕ} {b : Fin n → V} (hb : LinearIndependent L b)
    {M X : Submodule (𝓞 L) V} (h1 : Sub M (Submodule.span (𝓞 L) (Set.range b)))
    (h2 : Sub (Submodule.span (𝓞 L) (Set.range b)) M) (h : Sub M X) :
    X.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := by
  obtain ⟨c, hc, h⟩ := h
  have h3 := (relIndex_smul hb (Ideal.span {c}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) h1 h2).1
  have hle : Ideal.span {c} • M ≤ X := by
    refine Submodule.smul_le.2 fun a ha x hx => ?_
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [mul_smul]
    exact X.smul_mem _ (h x hx)
  exact ne_zero_of_dvd_ne_zero h3 (AddSubgroup.relIndex_dvd_of_le_left _ fun x hx => hle hx)

theorem log_relIndex_sub {G : Type} [AddCommGroup G] (X Y B : AddSubgroup G) (hYX : Y ≤ X)
    (h1 : B.relIndex Y ≠ 0) (h2 : Y.relIndex B ≠ 0) (h3 : Y.relIndex X ≠ 0) :
    Real.log (B.relIndex X : ℕ) - Real.log (X.relIndex B : ℕ) =
      Real.log (B.relIndex Y : ℕ) - Real.log (Y.relIndex B : ℕ) + Real.log (Y.relIndex X : ℕ) := by
  have e1 := AddSubgroup.relIndex_mul_relIndex (B ⊓ Y) Y X inf_le_right hYX
  have e2 := AddSubgroup.relIndex_mul_relIndex (B ⊓ Y) (B ⊓ X) X (inf_le_inf_left _ hYX) inf_le_right
  have e3 := AddSubgroup.relIndex_mul_relIndex (B ⊓ Y) (B ⊓ X) B (inf_le_inf_left _ hYX) inf_le_left
  rw [AddSubgroup.inf_relIndex_right] at e1 e2
  rw [AddSubgroup.inf_relIndex_left B X, AddSubgroup.inf_relIndex_left B Y] at e3
  rw [← e1] at e2
  have h4 : (B ⊓ Y).relIndex (B ⊓ X) ≠ 0 := left_ne_zero_of_mul (e3 ▸ h2)
  have h5 : X.relIndex B ≠ 0 := right_ne_zero_of_mul (e3 ▸ h2)
  have h6 : B.relIndex X ≠ 0 := right_ne_zero_of_mul (e2 ▸ mul_ne_zero h1 h3)
  have f2 := congrArg (fun m : ℕ => Real.log (m : ℝ)) e2
  have f3 := congrArg (fun m : ℕ => Real.log (m : ℝ)) e3
  simp only [Nat.cast_mul] at f2 f3
  rw [Real.log_mul (Nat.cast_ne_zero.2 h4) (Nat.cast_ne_zero.2 h6),
    Real.log_mul (Nat.cast_ne_zero.2 h1) (Nat.cast_ne_zero.2 h3)] at f2
  rw [Real.log_mul (Nat.cast_ne_zero.2 h4) (Nat.cast_ne_zero.2 h5)] at f3
  linarith

theorem logIdx_of_le {n : ℕ} {b : Fin n → V} (hb : LinearIndependent L b) {X Y : Submodule (𝓞 L) V} (hYX : Y ≤ X)
    (h1 : Sub X (Submodule.span (𝓞 L) (Set.range b))) (h2 : Sub (Submodule.span (𝓞 L) (Set.range b)) Y) :
    logIdx X b = logIdx Y b + Real.log (Y.toAddSubgroup.relIndex X.toAddSubgroup : ℕ) := by
  have hY := (Sub.of_le hYX).trans h1
  refine log_relIndex_sub _ _ _ (fun x hx => hYX hx) (relIndex_ne_zero hb hY h2 hY)
    (relIndex_ne_zero hb (Sub.of_le le_rfl) (Sub.of_le le_rfl) h2)
    (relIndex_ne_zero hb h1 (h2.trans (Sub.of_le hYX)) (h1.trans h2))

theorem logIdx_sub_le {n : ℕ} {b : Fin n → V} (hb : LinearIndependent L b) (𝔞 : Ideal (𝓞 L)) (h𝔞 : 𝔞 ≠ ⊥)
    {M F : Submodule (𝓞 L) V} (h1 : Sub M (Submodule.span (𝓞 L) (Set.range b)))
    (h2 : Sub (Submodule.span (𝓞 L) (Set.range b)) M) (h3 : Sub F (Submodule.span (𝓞 L) (Set.range b)))
    (h : 𝔞 • M ≤ F) : logIdx M b - logIdx F b ≤ n * Real.log (Ideal.absNorm 𝔞) := by
  have h4 : Sub (Submodule.span (𝓞 L) (Set.range b)) (𝔞 • M) := h2.trans (Sub.of_smul_le h𝔞 le_rfl)
  have e1 := logIdx_of_le hb (Submodule.smul_le_right (I := 𝔞) (N := M)) h1 h4
  have e2 := logIdx_of_le hb h h3 h4
  obtain ⟨h5, h6⟩ := relIndex_smul hb 𝔞 h𝔞 h1 h2
  have h7 : Real.log (((𝔞 • M).toAddSubgroup.relIndex M.toAddSubgroup : ℕ) : ℝ) ≤ n * Real.log (Ideal.absNorm 𝔞) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h5) (by exact_mod_cast h6)
  have h8 := Real.log_natCast_nonneg ((𝔞 • M).toAddSubgroup.relIndex F.toAddSubgroup)
  linarith

section Pt

variable {E Ψ : Type} [Field E] [NumberField E] (A : LinPt E L Ψ V)

theorem eig_fg (s : Ψ ⊕ Ψ) : (A.eig s).FG := A.fg.of_le inf_le_left

theorem exists_smul_mem_eig (s : Ψ ⊕ Ψ) {x : V} (hx : x ∈ eigSp A.ρ (A.σ s)) :
    ∃ c : 𝓞 L, c ≠ 0 ∧ c • x ∈ A.eig s := by
  obtain ⟨c, hc, h⟩ := exists_smul_mem_of_mem_span A.Λ (S := (A.Λ : Set V)) (fun _ h => h) (p := x)
    (A.span ▸ Submodule.mem_top)
  exact ⟨c, hc, h, ((eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)).smul_mem c hx⟩

theorem sub_eig {s : Ψ ⊕ Ψ} {n : ℕ} {b : Fin n → V} (hb : Submodule.span L (Set.range b) = eigSp A.ρ (A.σ s)) :
    Sub (A.eig s) (Submodule.span (𝓞 L) (Set.range b)) ∧ Sub (Submodule.span (𝓞 L) (Set.range b)) (A.eig s) := by
  refine ⟨Sub.of_fg (eig_fg A s) fun x hx => ?_, Sub.of_fg (Submodule.fg_span (Set.finite_range b)) fun x hx => ?_⟩
  · refine exists_smul_mem_of_mem_span _ (fun y hy => Submodule.subset_span hy) ?_
    rw [hb]
    exact hx.2
  · refine exists_smul_mem_eig A s ?_
    rw [← hb]
    exact Submodule.span_le_restrictScalars (𝓞 L) L _ hx

end Pt

end LevelTowerAlt
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.IsotropicSubmoduleNonzeroFamily
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

theorem isotropic_submodule_nonzero_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), IsCMFam σ → IsIsoSub R.form I → I ≠ ⊥ → (∃ r v, IsNzFamily I r v) ∧ ∀ r v, IsNzFamily I r v → R.nz σ I = R.nzOf σ I v ∧ 0 < R.nz σ I ∧ r = Module.finrank (𝓞 E) I := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ I hσ hI hne
  have := R.free
  have := R.fin
  refine ⟨exists_family hne, fun r v hv => ⟨nz_eq R hσ hv, ?_, family_rank hv⟩⟩
  rw [nz_eq R hσ hv]
  exact nzOf_pos R σ hI hv

end LevelTowerAlt
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.NefFibresScaledLattice
section
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TiePrimes

namespace LevelTowerAlt

namespace N1

section

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem homog_sub {a b : MRing J} {d : K → ℕ} (ha : IsMultiHomog a d) (hb : IsMultiHomog b d) :
    IsMultiHomog (a - b) d := by
  have h := homog_add ha (homog_mul (homog_C (J := J) (-1)) hb |> fun h => (zero_add d) ▸ h)
  have e : a + C (-1) * b = a - b := by simp [sub_eq_add_neg]
  rwa [e] at h

theorem cMon_notMem {W : Ideal (MRing J)} (hW : W.IsPrime) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    (d : K → ℕ) : cMon c d ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).1 h
  exact hc k (hW.mem_of_pow_mem _ hk)

theorem aeval_cMon (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (d : K → ℕ) :
    aeval y (cMon c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [cMon]

theorem exists_rep (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (lam : Ω) (hl : lam ≠ 0) (b : K → ℤ)
    (h1 : lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) ∈ (dh y c).range) (h2 : (lam * ∏ k, y ⟨k, c k⟩ ^ (-b k))⁻¹ ∈ (dh y c).range) :
    ∃ (F G : MRing J) (dF dG : K → ℕ), IsMultiHomog F dF ∧ IsMultiHomog G dG ∧ (∀ k, (dF k : ℤ) = dG k + b k) ∧
      aeval y F = lam * aeval y G ∧
      ∀ W : Ideal (MRing J), W.IsPrime → mCoordIdeal y ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → F ∉ W ∧ G ∉ W := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨f', hf'⟩ := h2
  obtain ⟨D, g, hg, e⟩ := exists_form_dh hc f
  obtain ⟨D', g', hg', e'⟩ := exists_form_dh hc f'
  replace e : dh y c g = lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) := e.trans hf
  replace e' : dh y c g' = (lam * ∏ k, y ⟨k, c k⟩ ^ (-b k))⁻¹ := e'.trans hf'
  have hw : lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) ≠ 0 :=
    mul_ne_zero hl (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k))
  refine ⟨g * cMon c (fun k => (b k).toNat), cMon c (D + fun k => (-b k).toNat), D + fun k => (b k).toNat, _,
    homog_mul hg (homog_cMon _ _), homog_cMon _ _, fun k => ?_, ?_, fun W hW hP hX => ⟨fun h => ?_, cMon_notMem hW hX _⟩⟩
  · simp only [Pi.add_apply]; push_cast; omega
  · rw [map_mul, aeval_eq_dh_mul y c hc hg, e, aeval_cMon, aeval_cMon, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k), ← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]; push_cast; omega
  · have hgW : g ∈ W := (hW.mem_or_mem h).resolve_right (cMon_notMem hW hX _)
    have hm : g * g' - cMon c (D + D') ∈ mCoordIdeal y := by
      rw [mem_coord_iff y (homog_sub (homog_mul hg hg') (homog_cMon _ _)), map_sub, map_mul,
        aeval_eq_dh_mul y c hc hg, aeval_eq_dh_mul y c hc hg', e, e', aeval_cMon, mul_mul_mul_comm,
        mul_inv_cancel₀ hw, one_mul, ← Finset.prod_mul_distrib]
      simp [pow_add]
    refine cMon_notMem hW hX (D + D') ?_
    have : cMon c (D + D') = g * g' - (g * g' - cMon c (D + D')) := by ring
    rw [this]
    exact W.sub_mem (W.mul_mem_right _ hgW) (hP hm)

theorem geoNum_one_add (W : Ideal (MRing J)) (a b : K → ℤ) :
    geoNum 1 W (fun _ => a + b) = geoNum 1 W (fun _ => a) + geoNum 1 W (fun _ => b) := by
  simp only [geoNum]
  split_ifs with h
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  · simp

theorem geoNum_eq_zero (y : (Σ k, J k) → Ω) (lam : Ω) (hl : lam ≠ 0) (b : K → ℤ)
    (h : ∀ c : ∀ k, J k, (∀ k, y ⟨k, c k⟩ ≠ 0) → lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) ∈ (dh y c).range ∧
      (lam * ∏ k, y ⟨k, c k⟩ ^ (-b k))⁻¹ ∈ (dh y c).range)
    (W : Ideal (MRing J)) (hW : IsMultiProjPrime W) (hP : mCoordIdeal y ≤ W) (hch : charOf W ≠ 0)
    (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    geoNum 1 W (fun _ => b) = 0 := by
  classical
  have rep : ∀ U : Ideal (MRing J), U.IsPrime → mCoordIdeal y ≤ U → IsRelevant U →
      ∃ (F G : MRing J) (dF dG : K → ℕ), IsMultiHomog F dF ∧ IsMultiHomog G dG ∧ (∀ k, (dF k : ℤ) = dG k + b k) ∧
      aeval y F = lam * aeval y G ∧ F ∉ U ∧ G ∉ U := by
    intro U hU hPU hr
    choose c hc using hr
    have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (hPU ((mem_coord_iff y (homog_X ⟨k, c k⟩)).2 (by simpa using h0)))
    obtain ⟨F, G, dF, dG, h1, h2, h3, h4, h5⟩ := exists_rep y c hy lam hl b (h c hy).1 (h c hy).2
    exact ⟨F, G, dF, dG, h1, h2, h3, h4, h5 U hU hPU hc⟩
  obtain ⟨F, G, dF, dG, hF, hG, hd, hFG, hFW, hGW⟩ := rep W hW.1 hP hW.2.2
  have hu : Flat.IsUnitSec W F G := by
    intro U hU hWU hr
    obtain ⟨F', G', dF', dG', hF', hG', hd', hFG', hFU, hGU⟩ := rep U hU (hP.trans hWU) hr
    refine ⟨G', F', hGU, hFU, hP ?_⟩
    have e : dF' + dG = dG' + dF := funext fun k => by
      have := hd k; have := hd' k; simp only [Pi.add_apply]; omega
    rw [mem_coord_iff y (homog_sub (homog_mul hG' hF) (e ▸ homog_mul hF' hG)), map_sub, map_mul, map_mul, hFG, hFG']
    ring
  have hs : divSupp W F = divSupp W G :=
    Set.Subset.antisymm (GlobalTheory.CompanionTheory.Ar.Flat.divSupp_subset_of_isUnitSec hu)
      (GlobalTheory.CompanionTheory.Ar.Flat.divSupp_subset_of_isUnitSec
        (GlobalTheory.CompanionTheory.Ar.Flat.IsUnitSec.symm hu))
  have hm : ∀ U ∈ divSupp W F, multAt (W ⊔ Ideal.span {F}) U =
      multAt (W ⊔ Ideal.span {G}) U := by
    rintro U ⟨hmin, hrel⟩
    have hUp : U.IsPrime := hmin.1.1
    obtain ⟨s, t, hs, ht, hst⟩ := hu U hUp (le_sup_left.trans hmin.1.2) hrel
    exact GlobalTheory.CompanionTheory.Ar.Flat.multAt_sup_span_eq_of_sub_mem hUp hs ht hst
  have hp := PB.prime_charOf_of_ne_zero hW.1 hch
  have hD : ∀ (d : K → ℕ) (s : MRing J), IsMultiHomog s d → s ∉ W →
      geoNum 1 W (fun _ => fun k => (d k : ℤ)) =
        ∑ᶠ U ∈ divSupp W s, (multAt (W ⊔ Ideal.span {s}) U : ℤ) * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ) := by
    intro d s hs hsW
    have hcut := GroundTheory.Heights₂.Heights.Inter.GeoNumCut.full K J W 0 Fin.elim0 d s hW hp (by rw [hdim]) hs hsW
    have hsn : (Fin.snoc (Fin.elim0 : Fin 0 → K → ℤ) (fun k => (d k : ℤ)) : Fin 1 → K → ℤ) =
        fun _ => fun k => (d k : ℤ) := by
      funext i
      rw [Fin.fin_one_eq_zero i]
      simp [Fin.snoc]
    rwa [hsn] at hcut
  have e1 : geoNum 1 W (fun _ => fun k => (dF k : ℤ)) = geoNum 1 W (fun _ => fun k => (dG k : ℤ)) := by
    rw [hD dF F hF hFW, hD dG G hG hGW, ← hs]
    exact finsum_mem_congr rfl fun U hU => by rw [hm U hU]
  have e2 : (fun k => (dF k : ℤ)) = (fun k => (dG k : ℤ)) + b := funext hd
  rw [e2, geoNum_one_add] at e1
  linarith

end

end N1

open N1

theorem nef_fibres_scaled_lattice : PB.Inputs → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (a a' : K → ℤ) (e e' u : Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → u ≠ 0 → L.IsDegOn Set.univ y a e → (L.scale u).IsDegOn Set.univ y a' e' → NefOnFibres (mCoordIdeal y) a → NefOnFibres (mCoordIdeal y) a' := by
  intro _ X Ω _ _ K _ J _ y ξ L a a' e e' u tie hu h h' hnef W hW hP hch hdim
  have hl : u * e / e' ≠ 0 := div_ne_zero (mul_ne_zero hu h.1) h'.1
  have h0 := geoNum_eq_zero y (u * e / e') hl (a' - a) (fun c hc => ?_) W hW hP hch hdim
  · have e2 : a' = a + (a' - a) := by abel
    rw [e2, geoNum_one_add, h0, add_zero]
    exact hnef W hW hP hch hdim
  have key : ∀ p : Cpt ξ, InChart ξ (seg y) c p →
      u * e / e' * ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k) ∈ regAt ξ p ∧
        (u * e / e' * ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k))⁻¹ ∈ regAt ξ p := by
    intro p hp
    have e1 := h.2 p trivial c hp
    have e2 := h'.2 p trivial c hp
    have e3 : Submodule.span (regAt ξ p) {u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)} =
        Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'} := by
      rw [← smul_eq_mul (∏ k, y ⟨k, c k⟩ ^ a' k), ← e2, Lat.scale, Lat.map, e1, Submodule.map_span, Set.image_singleton]
      rfl
    have n1 : ∏ k, y ⟨k, c k⟩ ^ a k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)
    have n2 : ∏ k, y ⟨k, c k⟩ ^ a' k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)
    have e4 : ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k) = (∏ k, y ⟨k, c k⟩ ^ a k) / ∏ k, y ⟨k, c k⟩ ^ a' k := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [← zpow_sub₀ (hc k)]; simp
    have he := h.1
    have he' := h'.1
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (e3 ▸ Submodule.mem_span_singleton_self _ :
      u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e) ∈ Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'})
    obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.1 (e3.symm ▸ Submodule.mem_span_singleton_self _ :
      (∏ k, y ⟨k, c k⟩ ^ a' k) * e' ∈ Submodule.span (regAt ξ p) {u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)})
    replace hr : (r : Ω) * ((∏ k, y ⟨k, c k⟩ ^ a' k) * e') = u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e) := hr
    replace hr' : (r' : Ω) * (u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) = (∏ k, y ⟨k, c k⟩ ^ a' k) * e' := hr'
    rw [e4]
    constructor
    · convert r.2 using 1
      field_simp
      linear_combination -hr
    · convert r'.2 using 1
      field_simp
      linear_combination -hr'
  rw [← adjoin_eq hc]
  exact ⟨(tie.ring c (seg_ne hc) _).2 fun p hp => (key p hp).1, (tie.ring c (seg_ne hc) _).2 fun p hp => (key p hp).2⟩

end LevelTowerAlt
end

