module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar

namespace GlobalTheory.Published

def ChernDegreeComplex : Prop :=
  ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), Presents Δ L r →
    ∀ φ : Weight Y.str (RingHom.id ℂ) L, φ.IsCInf →
      φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧
        φ.chernInt Y.dim Set.univ (fun _ => 1) = (Y.inter (fun _ => Δ) : ℝ)

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCuspidalNeZero
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SiegelSet.Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem torus_eq_one (h : IsCMExt F E σ) {X Y : Matrix (Fin n) (Fin 0) E} {t : Fin 0 → ℝ} {a : GAd σ J}
    (ha : IsTorusElt σ J X Y t a) : a = 1 := by
  refine GAd_ext σ J (fun w => ?_) fun v => by rw [mem_infPts_iff_forall.1 ha.1 v, map_one]
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  apply (archEquiv J h τ).injective
  rw [map_one, map_one]
  refine Subtype.ext (Units.ext ?_)
  rw [← GlobalTheory.Orb.archMat_eq_archEquiv J h]
  ext i j
  have := congrFun ((ha.2 w τ).2.2 (Pi.single j 1) (Subsingleton.elim _ _) (Subsingleton.elim _ _)) i
  simpa [mulVec, dotProduct, Pi.single_apply, apply_ite, Matrix.one_apply] using this

theorem compact_quotient (hP : GlobalTheory.Published.SiegelSetUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {X Y : Matrix (Fin n) (Fin 0) E} (hW : IsWittFrame σ J X Y) :
    ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ C, g = γ * s := by
  obtain ⟨K, Ω, c, hK, hΩ, -, -, -, -, hcov, -⟩ := hP F E σ h n J hJ 0 X Y hW
  refine ⟨_, hΩ.mul hK, fun g => ?_⟩
  obtain ⟨γ, hγ, _, ⟨p, hp, t, -, a, ha, k, hk, rfl⟩, e⟩ := hcov g
  exact ⟨γ, hγ, _, ⟨p, hp, k, hk, rfl⟩, by rw [e, torus_eq_one h ha, mul_one]⟩

end GlobalTheory.SiegelSet.Model

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich
section
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Formalism.UG

namespace GlobalTheory

namespace WeylCell

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

def IsWeylRep (w : Equiv.Perm (Fin n)) (x : GL (Fin n) R) : Prop :=
  ∀ i j, i ≠ w j → (x : Matrix (Fin n) (Fin n) R) i j = 0

def cell (x : GL (Fin n) R) : Subgroup (GL (Fin n) R) :=
  unipB R (Fin n) ⊓ (unipBLower R (Fin n)).comap (MulAut.conj x⁻¹).toMonoidHom

theorem mem_unipBLower {g : GL (Fin n) R} :
    g ∈ unipBLower R (Fin n) ↔ (∀ i j, i < j → (g : Matrix (Fin n) (Fin n) R) i j = 0) ∧
      ∀ i, (g : Matrix (Fin n) (Fin n) R) i i = 1 := by
  refine (mem_unipRad (e := opp (points (Fin n)))).trans (and_congr Iff.rfl ⟨fun h i => ?_, fun h i _ _ => ?_⟩)
  · exact (h i () ()).trans (by simp)
  · exact (h i).trans (by simp)

theorem mem_cell {x u : GL (Fin n) R} :
    u ∈ cell x ↔ u ∈ unipB R (Fin n) ∧ x⁻¹ * u * x ∈ unipBLower R (Fin n) := by
  simp [cell, Subgroup.mem_inf, Subgroup.mem_comap]

theorem isClosed_cell [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (x : GL (Fin n) R) :
    IsClosed (cell x : Set (GL (Fin n) R)) := by
  have key : ∀ (f : GL (Fin n) R → GL (Fin n) R), Continuous f → ∀ i j (c : R),
      IsClosed {u | (f u : Matrix (Fin n) (Fin n) R) i j = c} := fun f hf i j c =>
    isClosed_eq ((Units.continuous_val.comp hf).matrix_elem i j) continuous_const
  have hc : Continuous fun u : GL (Fin n) R => x⁻¹ * u * x := by fun_prop
  have e : (cell x : Set (GL (Fin n) R)) =
      ((⋂ i, ⋂ j, ⋂ _ : j < i, {u : GL (Fin n) R | (u : Matrix (Fin n) (Fin n) R) i j = 0}) ∩
        ⋂ i, {u : GL (Fin n) R | (u : Matrix (Fin n) (Fin n) R) i i = 1}) ∩
      ((⋂ i, ⋂ j, ⋂ _ : i < j, {u : GL (Fin n) R | ((x⁻¹ * u * x : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j = 0}) ∩
        ⋂ i, {u : GL (Fin n) R | ((x⁻¹ * u * x : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i = 1}) := by
    ext u
    simp only [SetLike.mem_coe, mem_cell, mem_unipB, mem_unipBLower, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq]
  rw [e]
  refine ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => key _ continuous_id i j 0).inter
    (isClosed_iInter fun i => key _ continuous_id i i 1)).inter
    ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => key _ hc i j 0).inter
    (isClosed_iInter fun i => key _ hc i i 1))


variable (R) in
abbrev permRep (w : Equiv.Perm (Fin n)) : GL (Fin n) R := (Matrix.permMatrixHom (R := R)).toHomUnits w

theorem permRep_apply (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    (permRep R w : Matrix (Fin n) (Fin n) R) i j = if i = w j then 1 else 0 := by
  simp [Matrix.permMatrixHom, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.Perm.inv_def, Equiv.symm_apply_eq]

theorem isWeylRep_permRep (w : Equiv.Perm (Fin n)) : IsWeylRep w (permRep R w) := fun _ _ h => by
  rw [permRep_apply, if_neg h]

end Ring

def cSL (Q z : ℂ) : ℂ := (1 - Q⁻¹ * z) / (1 - z)

def cSU (q z : ℂ) : ℂ := (1 - (q ^ 2)⁻¹ * z) * (1 + q⁻¹ * z) / (1 - z ^ 2)

abbrev lo {n : ℕ} (i : Fin (n / 2)) : Fin n := Fin.castLE (Nat.div_le_self n 2) i

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def cellU {σ : L →+* L} {n : ℕ} (x : GU σ n) : Subgroup (GU σ n) :=
  (cell (x : GL (Fin n) L)).subgroupOf (GU σ n)

end Unitary

end WeylCell

namespace Published

open WeylCell

end Published

namespace WeylCell

theorem exists_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K N : Subgroup G}
    (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (hN : IsClosed (N : Set G))
    [MeasurableSpace N] [BorelSpace N] : ∃ μ : Measure N, μ.IsHaarMeasure ∧ μ (K.subgroupOf N) = 1 := by
  have h1 : IsOpen (K.subgroupOf N : Set N) := ho.preimage continuous_subtype_val
  have h2 : IsCompact (K.subgroupOf N : Set N) := hN.isClosedEmbedding_subtypeVal.isCompact_preimage hc
  let P : TopologicalSpace.PositiveCompacts N := ⟨⟨_, h2⟩, by
    rw [show interior ((⟨_, h2⟩ : TopologicalSpace.Compacts N).carrier) = (K.subgroupOf N : Set N) from h1.interior_eq]
    exact ⟨1, one_mem _⟩⟩
  haveI : LocallyCompactSpace N := h2.locallyCompactSpace_of_mem_nhds_of_group (h1.mem_nhds (one_mem _))
  exact ⟨Measure.haarMeasure P, inferInstance, Measure.haarMeasure_self⟩

theorem exists_data_U {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (n : ℕ) (α : Fin (n / 2) → ℂˣ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, w i.rev = (w i).rev) :
    (∃ φ : GU σ n → ℂ, IsSphericalU q (fun i => (α i : ℂ)) φ ∧ φ 1 = 1) ∧
      (∃ x : GU σ n, x ∈ KU σ n ∧ IsWeylRep w (x : GL (Fin n) L)) ∧
      ∀ (x : GU σ n) [MeasurableSpace (cellU x)] [BorelSpace (cellU x)],
        ∃ μ : Measure (cellU x), μ.IsHaarMeasure ∧ μ ((KU σ n).subgroupOf (cellU x)) = 1 := by
  obtain ⟨ho, hc⟩ := LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n h
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) h (by omega) (by omega) (fun i => (α i : ℂ))
    fun i => (α i).ne_zero
  have hx : permRep L w ∈ GU σ n := by
    rw [LGrp.mem_GU_iff]
    intro i j
    rw [← map_inv, permRep_apply, permRep_apply, hw, apply_ite σ, map_one, map_zero]
    simp only [Fin.rev_inj, Equiv.Perm.eq_inv_iff_eq, eq_comm (a := j)]
  refine ⟨⟨φ, hφ, h1⟩, ⟨⟨_, hx⟩, ⟨hx, permRep _ w, ?_⟩, isWeylRep_permRep w⟩,
    fun x _ _ => exists_haar ho hc ((isClosed_cell _).preimage continuous_subtype_val)⟩
  ext i j
  show (intL L).subtype ((permRep _ w).val i j) = (permRep L w).val i j
  simp only [permRep_apply, apply_ite (intL L).subtype, map_one, map_zero]

end WeylCell

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy

namespace GlobalTheory.Published

def PointSeparationPair : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p
    ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (r : ℕ) (N₀ : LB X) (x₁ x₂ : X) (c : ℕ → ℝ),
      M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G →
      0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ →
      (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) =
        interNumRed ℂ C ![toLB G] / m + interNumRed ℂ C ![N₀] / r) →
      IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ →
      (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x₁ ∈ Z ∨ x₂ ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e ≤ 1 →
      ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s)

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.Published

def SiegelEisensteinDoubled : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ (B : Base F E) (n : ℕ), 1 ≤ n →
  ∀ W : Spc F E n, (∀ i j, σ (W.J j i) = -W.J i j) → W.L.IsLattice E →
    (∀ y, y ∈ W.L ↔ ∀ x ∈ W.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ W.J y x))) →
    (∀ w, IsCartan (Complex.I • W.J.map (B.emb w).1) (W.θ w)) →
  ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
  ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
  ∀ χ : Chr F E, IsHecke F E χ →
  ∀ (s₁ : ℂ) (φ : UA σ W₂.J → ℂ), φ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χ s₁ →
    let P : Subgroup (UA σ W₂.J) := siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype
    let f : ℂ → UA σ W₂.J → ℂ := flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ s₁
    ∃ Ei : ℂ → UA σ W₂.J → ℂ,
      (∀ s : ℂ, (n : ℝ) / 2 < s.re → ∀ g,
        Eis.CosetConv P (ratU σ W₂.J) (f s) g ∧ Ei s g = Eis.cosetSum P (ratU σ W₂.J) (f s) g) ∧
      ∀ s₀ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → UA σ W₂.J → ℂ), 0 < r ∧
        (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Ei s g) ∧
        (∀ g, DifferentiableOn ℂ (fun s => H s g) (Metric.ball s₀ r)) ∧
        ContinuousOn (fun x : ℂ × UA σ W₂.J => H x.1 x.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
        ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ r, ∀ g, ‖H s g‖ ≤ C * (ht g : ℝ) ^ N

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.Published

def SiegelWeilAnisotropicHermitian : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ B : Base F E, IsCharAF F B.ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ W : Spc F E n, (∀ i j, σ (W.J j i) = -W.J i j) → W.L.IsLattice E →
    (∀ y, y ∈ W.L ↔ ∀ x ∈ W.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ W.J y x))) →
    (∀ w, IsCartan (Complex.I • W.J.map (B.emb w).1) (W.θ w)) →
  ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
  ∀ X : Spc F E m, (∀ i j, σ (X.J j i) = X.J i j) → (∀ x, form σ X.J x x = 0 → x = 0) →
  ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)) (Fin m × Fin (n + n)),
    (∀ x : Matrix (Fin m) (Fin (n + n)) E, ∃ y z : Fin m × Fin (n + n) → F,
      co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
    (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : Rep σ X W₂, IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J) co χ 1 om →
  ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)).subtype (absE F E) K →
  ∀ Φ ∈ schA F (Fin m × Fin (n + n)), FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ X.J)) (𝓕 : Set (UA σ X.J)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ X.J) 𝓕 ν →
    let P : Subgroup (UA σ W₂.J) := siegelOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)).subtype
    let s₀ : ℂ := ((m : ℂ) - (n : ℂ)) / 2
    let f : ℂ → UA σ W₂.J → ℂ :=
      flatOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)).subtype (absE F E) K (fun g => om (1, g) Φ 0) s₀
    (∀ g, IntegrableOn (fun h => theta om Φ h g) 𝓕 ν) ∧
    (∀ s : ℂ, (n : ℝ) / 2 < s.re →
      AutomorphicL2Unitary.LeftInv (P ⊓ ratU σ W₂.J) (f s) ∧ ∀ g, Eis.CosetConv P (ratU σ W₂.J) (f s) g) ∧
    ∀ g, Cont.HolValueAt (fun s => Eis.cosetSum P (ratU σ W₂.J) (f s) g) s₀
      ((if n < m then 1 else 2 : ℂ) * ⨍ h in 𝓕, theta om Φ h g ∂ν)

end GlobalTheory.Published

end
end

