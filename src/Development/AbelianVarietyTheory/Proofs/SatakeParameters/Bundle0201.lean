module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.EigTwist

open scoped Matrix

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

def sumL (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) : Σ m : ℕ, Γ →* GL (Fin m) K :=
  L.foldr (fun p s => ⟨p.1 + s.1, Formalism.MainNotions.SumRepresentations.At.sumRep p.2 s.2⟩) ⟨0, 1⟩

theorem isSSRep_sumL : ∀ L : List (Σ m : ℕ, Γ →* GL (Fin m) K), (∀ p ∈ L, IsSSRep p.2) →
    IsSSRep (sumL L).2
  | [], _ => GlobalTheory.BCGal.ss_zero _
  | p :: L, h => GlobalTheory.BCGal.ss_sumRep _ _ (h p List.mem_cons_self)
      (isSSRep_sumL L fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem charpoly_sumRep {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K).charpoly =
      ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K).charpoly *
        ((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K).charpoly := by
  rw [GlobalTheory.BCGal.sumRep_val, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂]

theorem charpoly_sumL : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ),
    (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K).charpoly =
      (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod
  | [], g => by
    rw [List.map_nil, List.prod_nil]
    exact Polynomial.eq_one_of_monic_natDegree_zero (Matrix.charpoly_monic _)
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; rfl)
  | p :: L, g => by
    rw [List.map_cons, List.prod_cons, ← charpoly_sumL L g]
    exact charpoly_sumRep p.2 (sumL L).2 g

theorem sumRep_mulVec_inl {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ)
    (w : Fin (a + b) → K) (i : Fin a) :
    (((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w)
      (finSumFinEquiv (Sum.inl i)) =
      (((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K) *ᵥ (w ∘ finSumFinEquiv ∘ Sum.inl)) i := by
  rw [GlobalTheory.BCGal.sumRep_val]
  simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem sumRep_mulVec_inr {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K) (g : Γ)
    (w : Fin (a + b) → K) (j : Fin b) :
    (((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w)
      (finSumFinEquiv (Sum.inr j)) =
      (((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K) *ᵥ (w ∘ finSumFinEquiv ∘ Sum.inr)) j := by
  rw [GlobalTheory.BCGal.sumRep_val]
  simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem eigen_pair (χ : Γ →* Kˣ) {a b : ℕ} (ρ : Γ →* GL (Fin a) K) (ρ' : Γ →* GL (Fin b) K)
    (w : Fin (a + b) → K) (hw : w ≠ 0)
    (he : ∀ g, ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) K) *ᵥ w =
      ((χ g : Kˣ) : K) • w) :
    (∃ v : Fin a → K, v ≠ 0 ∧ ∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) K) *ᵥ v = ((χ g : Kˣ) : K) • v) ∨
    (∃ v : Fin b → K, v ≠ 0 ∧ ∀ g, ((ρ' g : GL _ _) : Matrix (Fin b) (Fin b) K) *ᵥ v = ((χ g : Kˣ) : K) • v) := by
  by_cases h1 : w ∘ finSumFinEquiv ∘ Sum.inl = 0
  · right
    refine ⟨w ∘ finSumFinEquiv ∘ Sum.inr, fun h2 => hw ?_, fun g => ?_⟩
    · funext j
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
      rcases s with i | i
      · exact congrFun h1 i
      · exact congrFun h2 i
    · funext j
      have h3 := congrFun (he g) (finSumFinEquiv (Sum.inr j))
      rw [sumRep_mulVec_inr] at h3
      rw [h3]
      simp
  · left
    refine ⟨w ∘ finSumFinEquiv ∘ Sum.inl, h1, fun g => ?_⟩
    funext i
    have h3 := congrFun (he g) (finSumFinEquiv (Sum.inl i))
    rw [sumRep_mulVec_inl] at h3
    rw [h3]
    simp

theorem eigen_sumL (χ : Γ →* Kˣ) : ∀ (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (w : Fin (sumL L).1 → K),
    w ≠ 0 → (∀ g, (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K) *ᵥ w =
      ((χ g : Kˣ) : K) • w) →
    ∃ p ∈ L, ∃ v : Fin p.1 → K, v ≠ 0 ∧
      ∀ g, ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K) *ᵥ v = ((χ g : Kˣ) : K) • v := by
  intro L
  induction L with
  | nil =>
    intro w hw _
    exact (hw (funext fun i => (Nat.not_lt_zero _ i.2).elim)).elim
  | cons p L ih =>
    intro w hw he
    rcases eigen_pair χ p.2 (sumL L).2 w hw he with ⟨v, hv0, hv⟩ | ⟨v, hv0, hv⟩
    · exact ⟨p, List.mem_cons_self, v, hv0, hv⟩
    · obtain ⟨q, hq, u, hu0, hu⟩ := ih v hv0 hv
      exact ⟨q, List.mem_cons_of_mem _ hq, u, hu0, hu⟩

theorem eigen_transfer {n m : ℕ} (ρ : Γ →* GL (Fin n) K) (σ : Γ →* GL (Fin m) K) (hρ : IsSSRep ρ)
    (hσ : IsSSRep σ)
    (hc : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K).charpoly)
    (χ : Γ →* Kˣ) (v : Fin n → K) (hv0 : v ≠ 0)
    (hv : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ v = ((χ g : Kˣ) : K) • v) :
    ∃ w : Fin m → K, w ≠ 0 ∧ ∀ g, ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K) *ᵥ w = ((χ g : Kˣ) : K) • w := by
  have hnm : n = m := by
    have h1 := congrArg Polynomial.natDegree (hc 1)
    rwa [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Fintype.card_fin] at h1
  subst hnm
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ σ hρ hσ hc
  refine ⟨((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ v, fun h0 => hv0 ?_, fun g => ?_⟩
  · have h1 := congrArg (fun u => ((P : GL _ _) : Matrix (Fin n) (Fin n) K) *ᵥ u) h0
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
  · rw [Matrix.mulVec_mulVec, hP g]
    have e : ((P⁻¹ * ρ g * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) =
        ((P⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) K) * ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [e, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]

end GlobalTheory.EigTwist


open GlobalTheory.EigTwist in
theorem GlobalTheory.eigenCharTwist_holds : EigenCharTwist := by
  intro K _ _ Γ _ n ρ L χ hρ hL hc hv
  obtain ⟨v, hv0, hv⟩ := hv
  have hS := isSSRep_sumL L hL
  have hcS : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      (((sumL L).2 g : GL _ _) : Matrix (Fin (sumL L).1) (Fin (sumL L).1) K).charpoly :=
    fun g => (hc g).trans (charpoly_sumL L g).symm
  obtain ⟨w, hw0, hw⟩ := eigen_transfer ρ (sumL L).2 hρ hS hcS χ v hv0 hv
  exact eigen_sumL χ L w hw0 hw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCentralScalarDistinctGeometricLemmaCells
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CellCentral

open scoped TensorProduct

theorem twKer_piTensor_eq_top {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (N : Subgroup (∀ a, Γ a)) (a : α) (Na : Subgroup (Γ a)) (hN : ∀ u ∈ Na, Pi.mulSingle a u ∈ N)
    (h : twKer (ρ a) Na 1 = ⊤) : twKer (piTensor ρ) N 1 = ⊤ := by
  refine eq_top_iff.2 fun y hy0 => ?_
  clear hy0
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => exact add_mem hx hy
  | smul_tprod r x =>
    refine Submodule.smul_mem _ r ?_
    let L := (PiTensorProduct.tprod ℂ : (∀ i, X i) →ₘₗ[ℂ] (⨂[ℂ] i, X i)).toLinearMap x a
    have hL : ∀ w, L w = PiTensorProduct.tprod ℂ (Function.update x a w) := fun w => rfl
    have hle : twKer (ρ a) Na 1 ≤ (twKer (piTensor ρ) N 1).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have hpi : piTensor ρ (Pi.mulSingle a (u : Γ a)) (PiTensorProduct.tprod ℂ (Function.update x a v)) =
          PiTensorProduct.tprod ℂ (Function.update x a (ρ a u v)) := by
        rw [piTensor_tprod]
        congr 1
        funext b
        by_cases hb : b = a
        · subst hb; simp
        · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
      refine Submodule.subset_span ⟨⟨_, hN u u.2⟩, PiTensorProduct.tprod ℂ (Function.update x a v), ?_⟩
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      rw [map_sub, hL, hL, hpi]
    have hx : x a ∈ twKer (ρ a) Na 1 := h ▸ Submodule.mem_top
    have := hle hx
    simpa [hL] using this

theorem deltaHalf_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (hm : ∀ a b, a ≠ b → IsEmpty (m a) ∨ IsEmpty (m b)) (g : Levi k m) : deltaHalf k m g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : IsEmpty (m a)
  · have : Matrix.GeneralLinearGroup.det (g a) = 1 := Units.ext (by simp [Matrix.det_isEmpty])
    rw [this, map_one]
  · have h0 : modExp m a = 0 := by
      unfold modExp
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
      · intro b hb
        have hne : b ≠ a := by rintro rfl; simp at hb
        have : IsEmpty (m b) := (hm a b hne.symm).resolve_left ha
        simp
      · intro b hb
        have hne : b ≠ a := by rintro rfl; simp at hb
        have : IsEmpty (m b) := (hm a b hne.symm).resolve_left ha
        simp
    simp [h0]

theorem smInd_central {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W]
    [Module ℂ W] (H : Subgroup G) (σ : Representation ℂ H W) (z : G) (hz : z ∈ H)
    (hcen : ∀ x, x * z = z * x) (c : ℂ) (hc : ∀ w, σ ⟨z, hz⟩ w = c • w) (F : smoothPart (ind H σ)) :
    smInd H σ z F = c • F := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  show F.1.1 (x * z) = c • F.1.1 x
  rw [hcen x]
  exact (F.1.2 ⟨z, hz⟩ x).trans (hc _)

theorem one_case (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (σ : Fin 2 → Irr k 1) (hσ : ∀ i, 0 < 1 ∧ IsCuspidal (σ i).π)
    (hnt : ¬ Nonempty ((σ 0).π.Equiv (twist (σ 1).π (detChar (Fin 1) (unrChar k 1))))) :
    ∃ (z : Levi k fun _ : Fin 2 => Fin 1) (c c' : ℂ), (∀ g, g * z = z * g) ∧ c ≠ c' ∧
      (∀ x, (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) z x = c • x) ∧
      ∀ (b : SizeMatrix (fun _ : Fin 2 => Fin 1) (fun _ : Fin 2 => Fin 1)),
        b.1 1 0 = 0 → ∀ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin 1)
          (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin 1) y,
          cellFunctor f g (piTensor fun i => (σ i).π) z y = c' • y := by
  have hact : ∀ i (ψ : kˣ →* ℂˣ), (σ i).π.Equiv (detRep (Fin 1) ψ) → ∀ (g : GL (Fin 1) k) v,
      (σ i).π g v = (ψ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    intro i ψ e g v
    apply EquivLike.injective e
    have h1 : e ((σ i).π g v) = detRep (Fin 1) ψ g (e v) :=
      LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v
    rw [h1, map_smul]
    simp [detRep, detChar_apply, smul_eq_mul]
  have h0 := RankLeOne.exists_equiv_detRep k (Fin 1) (σ 0).V (σ 0).π (σ 0).smooth (σ 0).irr
  have h1 := RankLeOne.exists_equiv_detRep k (Fin 1) (σ 1).V (σ 1).π (σ 1).smooth (σ 1).irr
  obtain ⟨ψ₀, -, ⟨e₀⟩⟩ := h0
  obtain ⟨ψ₁, -, ⟨e₁⟩⟩ := h1
  have hψ : ∃ t, ψ₀ t ≠ ψ₁ t := by
    by_contra hc
    push_neg at hc
    have hu : unrChar k 1 = 1 := MonoidHom.ext fun x => by simp [unrChar_apply]
    have hdet : detChar (Fin 1) (1 : kˣ →* ℂˣ) = (1 : GL (Fin 1) k →* ℂˣ) :=
      MonoidHom.ext fun x => by simp
    have hψe : ψ₀ = ψ₁ := MonoidHom.ext hc
    subst hψe
    rw [hu, hdet, twist_one] at hnt
    exact hnt ⟨e₀.trans e₁.symm⟩
  obtain ⟨t, ht⟩ := hψ
  let z : Levi k fun _ : Fin 2 => Fin 1 := Pi.mulSingle 0 (Matrix.GeneralLinearGroup.scalar (Fin 1) t)
  have hcomm : ∀ (g h : GL (Fin 1) k), g * h = h * g := by
    intro g h
    ext a b
    fin_cases a; fin_cases b
    simp [Matrix.mul_apply, mul_comm]
  have hcen : ∀ g, g * z = z * g := fun g => funext fun j => hcomm _ _
  refine ⟨z, ψ₁ t, ψ₀ t, hcen, fun h => ht (Units.ext h).symm, ?_, ?_⟩
  · intro x
    apply GlobalTheory.ProdSupport.piTensor_mulSingle _ 0 _ _ _ x
    intro v
    have hs : Equiv.swap (0 : Fin 2) 1 0 = 1 := Equiv.swap_apply_left 0 1
    rw [hact _ ψ₁ (hs ▸ e₁),
      GlobalTheory.ProdSupport.det_scalar_one rfl]
  · intro b hb f g y
    have hr0 := b.2.1 0
    have hr1 := b.2.1 1
    have hc0 := b.2.2 0
    have hc1 := b.2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin] at hr0 hr1 hc0 hc1
    have h01 : b.1 0 1 = 0 := by omega
    have hoff : ∀ i j : Fin 2, i ≠ j → b.1 i j = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hemp : ∀ i j : Fin 2, i ≠ j → IsEmpty (Fin (b.1 i j)) := fun i j hij => by
      rw [hoff i j hij]; infer_instance
    have hz : z ∈ relParab k g := by
      refine (Subgroup.mem_pi _).2 fun j _ => mem_parab.2 fun p q hpq => ?_
      rw [Subsingleton.elim p q] at hpq
      exact absurd hpq (lt_irrefl _)
    have hA : relDeltaHalf k (fun j i => Fin (b.1 i j)) (relProj k g ⟨z, hz⟩) = 1 := by
      rw [relDeltaHalf_apply]
      refine Finset.prod_eq_one fun j _ => deltaHalf_eq_one _ (fun a a' haa' => ?_) _
      by_cases h : a = j
      · subst h; exact Or.inr (hemp a' a (Ne.symm haa'))
      · exact Or.inl (hemp a j h)
    have hB : ∀ P, relDeltaHalf k (fun i j => Fin (b.1 i j)) P = 1 := by
      intro P
      rw [relDeltaHalf_apply]
      refine Finset.prod_eq_one fun i _ => deltaHalf_eq_one _ (fun a a' haa' => ?_) _
      by_cases h : a = i
      · subst h; exact Or.inr (hemp a a' haa')
      · exact Or.inl (hemp i a (Ne.symm h))
    have hC : relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g ⟨z, hz⟩)) =
        (Pi.mulSingle (0 : Fin 2) (Matrix.GeneralLinearGroup.scalar (Fin 1) t) : Levi k fun _ : Fin 2 => Fin 1) := by
      funext i
      ext p q
      obtain rfl : p = q := Subsingleton.elim p q
      obtain ⟨⟨j, r⟩, hr⟩ := (f i).surjective p
      subst hr
      rw [relEmb_apply, leviEmb_apply_same]
      have hij : i = j := by
        by_contra hne
        have := r.2
        have h0 := hoff i j hne
        omega
      subst hij
      show ((z i : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) (g i ⟨i, r⟩) (g i ⟨i, r⟩) = _
      rw [Subsingleton.elim (g i ⟨i, r⟩) (f i ⟨i, r⟩)]
    refine smInd_central _ _ z hz hcen _ (fun w => ?_) y
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    simp only [MonoidHom.comp_apply, twist_apply, relJac_mk, hA, hB, hC, inv_one, Units.val_one, one_smul]
    rw [GlobalTheory.ProdSupport.piTensor_mulSingle _ 0 _ _ (hact 0 ψ₀ e₀ _), GlobalTheory.ProdSupport.det_scalar_one rfl,
      Submodule.Quotient.mk_smul]

theorem exists_central_scalar_ne_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 →
    (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) →
    ∃ (z : Levi k fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))) (c c' : ℂ), (∀ g, g * z = z * g) ∧ c ≠ c' ∧
      (∀ x, (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) z x = c • x) ∧
      ∀ (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j)))),
        b.1 1 0 = 0 → ∀ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i))
          (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))) y,
          cellFunctor f g (piTensor fun i => (σ i).π) z y = c' • y := by
  intro k _ _ _ _ d σ hσ hd1 hnt
  by_cases hd0 : d 0 = 1
  · have hd : d = fun _ => 1 := by
      funext i
      fin_cases i
      · exact hd0
      · exact hd1
    subst hd
    exact one_case k σ hσ (hnt rfl 1)
  · refine ⟨1, 1, 2, fun g => by simp, by norm_num, fun x => by simp, ?_⟩
    intro b hb f g y
    have hr0 := b.2.1 0
    have hr1 := b.2.1 1
    have hc0 := b.2.2 0
    have hc1 := b.2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at hr0 hr1 hc0 hc1
    have hpos := (hσ 0).1
    have h00 : b.1 0 0 = 1 := by omega
    have h01 : 0 < b.1 0 1 := by omega
    have hne : unipRad k (f 0) ≠ ⊥ := by
      refine CuspMax.unipRad_ne_bot_iff.2 ⟨f 0 ⟨0, ⟨0, by omega⟩⟩, f 0 ⟨1, ⟨0, h01⟩⟩, ?_⟩
      simp
    have hJ : twKer (σ 0).π (unipRad k (f 0)) 1 = ⊤ :=
      Submodule.Quotient.subsingleton_iff.1 ((hσ 0).2.2 2 (b.1 0) (f 0) hne)
    have hT : twKer (piTensor fun i => (σ i).π) (relUnip k f) 1 = ⊤ := by
      refine twKer_piTensor_eq_top _ _ 0 _ (fun u hu => ?_) hJ
      refine (Subgroup.mem_pi _).2 fun i _ => ?_
      by_cases hi : i = 0
      · subst hi; simpa using hu
      · rw [Pi.mulSingle_eq_of_ne hi]; exact one_mem _
    haveI : Subsingleton (Jacquet (piTensor fun i => (σ i).π) (relUnip k f)) :=
      Submodule.Quotient.subsingleton_iff.2 hT
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact Subsingleton.elim (α := Jacquet (piTensor fun i => (σ i).π) (relUnip k f)) _ _

end GlobalTheory.CellCentral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantZmodLift
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

open Matrix

namespace GlobalTheory.EllU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* UA E n where
  toFun g := ⟨finGL E n (GeneralLinearGroup.map (pFin E) g.1),
    GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin g)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem finPart_mem (g : UA E n) : finPart g ∈ finU (E := E) (n := n) := pInf_finGL _

theorem finPart_of_finU {k : UA E n} (hk : k ∈ finU (E := E) (n := n)) : finPart k = k :=
  Subtype.ext (GlobalTheory.DefU.ClassFin.finGL_pFin ⟨k, hk⟩)

theorem finPart_of_infU {x : UA E n} (hx : x ∈ infU E n) : finPart x = 1 := by
  have h : GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  refine Subtype.ext ?_
  change finGL E n (GeneralLinearGroup.map (pFin E) x.1) = 1
  rw [h, map_one]

theorem inv_finPart_mul_mem (g : UA E n) : (finPart g)⁻¹ * g ∈ infU E n := by
  change GeneralLinearGroup.map (pFin E) ((finPart g)⁻¹ * g).1 = 1
  have h : GeneralLinearGroup.map (pFin E) (finPart g).1 = GeneralLinearGroup.map (pFin E) g.1 := pFin_finGL _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, inv_mul_cancel]

theorem continuous_finPart : Continuous (finPart (E := E) (n := n)) := by
  have h1 : Continuous (GeneralLinearGroup.map (pFin E) : GA E n → GL (Fin n) (Af E)) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
  exact Continuous.subtype_mk (GlobalTheory.DefU.ClassFin.continuous_finGL.comp (h1.comp continuous_subtype_val)) _

end GlobalTheory.EllU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterIndependentOfLocalEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Pst.BridgeWD

theorem wdAt_bridge_indep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Loc.Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r → GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O O' _ _ _ _ _ _ Bw Bw' hj hj' a r hc hr hr'
  exact GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge l P AI hT ι E Ω A w O O' Bw Bw' h hj hj' a r hc hr hr'

end GlobalTheory.Pst.BridgeWD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GalRepRankTwo
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalFirstClause

open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp


end GlobalTheory.GalFirstClause
end
end

