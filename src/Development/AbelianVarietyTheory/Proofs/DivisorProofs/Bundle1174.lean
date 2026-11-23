module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTranscendenceBasisOverConstEqOfAlgEquiv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem GlobalTheory.trBasis_card_eq_of_algEquiv : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (e : K ≃ₐ[ℂ] κ)
  (n k : ℕ) (x : Fin n → K) (z : Fin k → κ),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ) z → n = k := by
  intro K κ _ _ _ _ e n k x z hx hz
  have eK : (algebraMap ℂ K).toAlgebra = (inferInstance : Algebra ℂ K) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have eκ : (algebraMap ℂ κ).toAlgebra = (inferInstance : Algebra ℂ κ) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis at hx hz
  rw [eK] at hx
  rw [eκ] at hz
  have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hz
  rw [Cardinal.mk_fin, e.trdeg_eq] at h1
  rw [Cardinal.mk_fin, ← h1] at h2
  exact_mod_cast h2.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellHeightLocalReduction
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Topology Pointwise

namespace GlobalTheory.WhitHered.CellLoc

section Alg

variable {k : Type} [Field k] {N : ℕ}

end Alg

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N c : ℕ} {m : Fin c → ℕ}

theorem isClosed_parab (e : (Σ a, Fin (m a)) ≃ Fin N) : IsClosed (parab k e : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : (parab k e : Set (GL (Fin N) k)) = ⋂ i, ⋂ j, ⋂ _ : blk e j < blk e i, {g : GL (Fin N) k | g.val i j = 0} := by
    ext g
    simp only [SetLike.mem_coe, mem_parab, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

end Main

end GlobalTheory.WhitHered.CellLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralSimpleAlgebraEmbeddingsConjugate
section
open MeasureTheory Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.VanishNonEll

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd GlobalTheory.LKCount GlobalTheory.LKCount.OrbKProd

section Transport

variable {A B : Type} [Group A] [Group B]

theorem map_twCent_id (e : A ≃* B) (δ : A) :
    (twCent (MonoidHom.id A) δ).map e.toMonoidHom = twCent (MonoidHom.id B) (e δ) := by
  ext b
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : a * δ = δ * a := ha
    show e a * e δ = e δ * e a
    rw [← map_mul, ha', map_mul]
  · intro hb
    have hb' : b * e δ = e δ * b := hb
    refine ⟨e.symm b, ?_, by simp⟩
    show e.symm b * δ = δ * e.symm b
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hb']

theorem map_conj_equiv (e : A ≃* B) (K : Subgroup A) (x : A) :
    (K.map (MulAut.conj x).toMonoidHom).map e.toMonoidHom =
      (K.map e.toMonoidHom).map (MulAut.conj (e x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext k
  simp [MulAut.conj_apply]

theorem orbK_congr_equiv (e : A ≃* B) (K : Subgroup A) (δ : A) (F : A → ℂ)
    (hinv : ∀ t ∈ twCent (MonoidHom.id B) (e δ), ∀ k ∈ K.map e.toMonoidHom, ∀ x,
      oTerm (MonoidHom.id B) (K.map e.toMonoidHom) (twCent (MonoidHom.id B) (e δ) ⊓ K.map e.toMonoidHom) (e δ)
          (fun z => F (e.symm z)) (t * x * k) =
        oTerm (MonoidHom.id B) (K.map e.toMonoidHom) (twCent (MonoidHom.id B) (e δ) ⊓ K.map e.toMonoidHom) (e δ)
          (fun z => F (e.symm z)) x) :
    orbK (MonoidHom.id A) K δ F = orbK (MonoidHom.id B) (K.map e.toMonoidHom) (e δ) (fun z => F (e.symm z)) := by
  unfold orbK
  rw [orbC_eq, orbC_eq]
  set TB := twCent (MonoidHom.id B) (e δ)
  set KB := K.map e.toMonoidHom
  have hmemT : ∀ a ∈ TB, e.symm a ∈ twCent (MonoidHom.id A) δ := by
    intro a ha
    rw [← show (twCent (MonoidHom.id A) δ).map e.toMonoidHom = TB from map_twCent_id e δ] at ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    simpa using ha'
  have hmemK : ∀ b ∈ KB, e.symm b ∈ K := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    simpa using hb'
  have hpt : ∀ x : A, oTerm (MonoidHom.id A) K (twCent (MonoidHom.id A) δ ⊓ K) δ F x =
      oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (e x) := by
    intro x
    unfold oTerm
    congr 1
    · have h1 : TB ⊓ KB = (twCent (MonoidHom.id A) δ ⊓ K).map e.toMonoidHom := by
        rw [Subgroup.map_inf_eq _ _ _ e.injective, map_twCent_id]
      have h2 : TB ⊓ KB.map (MulAut.conj (e x)).toMonoidHom =
          (twCent (MonoidHom.id A) δ ⊓ K.map (MulAut.conj x).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_inf_eq _ _ _ e.injective, map_twCent_id, map_conj_equiv]
      rw [h1, h2]
      unfold vol
      rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective,
        Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    · simp
  let Φ : DoubleCoset.Quotient (twCent (MonoidHom.id A) δ : Set A) (K : Set A) →
      DoubleCoset.Quotient (TB : Set B) (KB : Set B) := fun q => DoubleCoset.mk TB KB (e (Quotient.out q))
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro q1 q2 h
      obtain ⟨a, ha, b, hb, h'⟩ := (@DoubleCoset.eq _ _ _ _ _ _).mp h
      calc q1 = DoubleCoset.mk _ K (Quotient.out q1) := (DoubleCoset.out_eq' q1).symm
        _ = DoubleCoset.mk _ K (Quotient.out q2) := by
          rw [DoubleCoset.eq]
          refine ⟨e.symm a, hmemT a ha, e.symm b, hmemK b hb, ?_⟩
          apply e.injective
          simp [h']
        _ = q2 := DoubleCoset.out_eq' q2
    · intro p
      refine ⟨DoubleCoset.mk (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p)), ?_⟩
      obtain ⟨a, ha, b, hb, h'⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p))
      show DoubleCoset.mk TB KB (e (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p))))) = p
      rw [h']
      conv_rhs => rw [← DoubleCoset.out_eq' p]
      rw [DoubleCoset.eq]
      have ha' : e a ∈ TB := by rw [← show (twCent (MonoidHom.id A) δ).map e.toMonoidHom = TB from map_twCent_id e δ]; exact Subgroup.mem_map_of_mem _ ha
      have hb' : e b ∈ KB := Subgroup.mem_map_of_mem _ hb
      refine ⟨(e a)⁻¹, TB.inv_mem ha', (e b)⁻¹, KB.inv_mem hb', ?_⟩
      simp [mul_assoc]
  have hz : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id A) δ : Set A) (K : Set A), oTerm (MonoidHom.id A) K (twCent (MonoidHom.id A) δ ⊓ K) δ F (Quotient.out q) =
      oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out (Equiv.ofBijective Φ hΦ q)) := by
    intro q
    rw [hpt]
    obtain ⟨a, ha, b, hb, h'⟩ := DoubleCoset.mk_out_eq_mul TB KB (e (Quotient.out q))
    show _ = oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out (DoubleCoset.mk TB KB (e (Quotient.out q))))
    rw [h', hinv a ha b hb]
  rw [finsum_congr hz]
  exact finsum_comp_equiv (Equiv.ofBijective Φ hΦ)
    (f := fun q => oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out q))

end Transport

section Prod

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
  [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]

end Prod

theorem natDegree_minpoly_le (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C]
    [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ) (hn : 0 < n)
    (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (a : C) : (minpoly F a).natDegree ≤ n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let g : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ι (fun l y ↦ Algebra.commute_algebraMap_left l _)
  haveI : IsSimpleRing (L ⊗[F] C) := GroundTheory.Brauer.isSimpleRing_tensorProduct_of_right
  have hg : Function.Injective g := GlobalTheory.CsaCharpoly.injective_of_isSimpleRing g.toRingHom
  have eg : g ((1 : L) ⊗ₜ a) = ι a := by
    simp only [g]; erw [Algebra.TensorProduct.lift_tmul]; simp
  have hyi : IsIntegral L ((1 : L) ⊗ₜ[F] a) := IsIntegral.of_finite L _
  have hmin : minpoly L (ι a) = minpoly L ((1 : L) ⊗ₜ[F] a) := by
    rw [← eg]; exact minpoly.algHom_eq g hg _
  have h1 := GlobalTheory.CsaCharpoly.natDegree_minpoly_le_one_tmul L a hyi
  rw [← hmin] at h1
  have h2 : (minpoly L (ι a)).natDegree ≤ (ι a).charpoly.natDegree :=
    Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly _) (Matrix.charpoly_monic _).ne_zero
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  omega

theorem not_irreducible_map {F L : Type} [Field F] [Field L] (φ : F →+* L) (p : Polynomial F) (hp : p.Monic)
    (hirr : ¬ Irreducible p) : ¬ Irreducible (p.map φ) :=
  fun h => hirr (Polynomial.Monic.irreducible_of_irreducible_map φ p hp h)

end GlobalTheory.VanishNonEll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedOffFinitePrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOff

theorem natCast_not_mem {D : D7} {S : Finset ℕ} {w : Pl D.host.E} (hw : Off S w) {N : ℕ} (hN : 0 < N)
    (hS : N.primeFactors ⊆ S) : ((N : 𝓞 D.host.E)) ∉ w.asIdeal := by
  intro h
  rw [← Nat.prod_factorization_pow_eq_self hN.ne', Nat.cast_finsuppProd] at h
  obtain ⟨p, hp, hpw⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 h
  dsimp only at hpw
  rw [Nat.cast_pow] at hpw
  exact hw p (hS (Nat.support_factorization N ▸ hp)) (w.isPrime.mem_of_pow_mem _ hpw)

theorem infPart_idem {D : D7} {e : AE D} (he : Formalism.L2.Theta.IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨hee, hec, v, ε, ⟨α, hε, -, -⟩, hs⟩ := he
  have h1 : e = e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← hs, mul_add, hee, hec, add_zero]
  have h2 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    subst hε
    have e1 : (algebraMap (AF D.host.F) (AE D)) (pairA D.host.F 0 α) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [e1]
    simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  rw [h1, map_mul, h2, mul_zero]

theorem intAE_one {D : D7} : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
  apply AddSubgroup.subset_closure
  exact ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩

theorem intAE_mul {D : D7} {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x h =>
    obtain ⟨a, ha, s, rfl⟩ := h
    induction hy using AddSubgroup.closure_induction with
    | mem y h' =>
      obtain ⟨b, hb, t, rfl⟩ := h'
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, s * t, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; push_cast; rfl
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [mul_neg]; exact neg_mem h1
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg x _ h1 => rw [neg_mul]; exact neg_mem h1

theorem unr_off : ∀ (D : D7) (c : (AE D)ˣ →* Circle), Continuous c →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e := by
  intro D c hc
  obtain ⟨N, hN, hN1, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc
  refine ⟨N.primeFactors, fun q hq => Nat.prime_of_mem_primeFactors hq, ?_⟩
  intro w hw e he x hx h1 h2
  have hNw := natCast_not_mem hw hN le_rfl
  have hN0 : ((N : 𝓞 D.host.E)) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hg : finPart D (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹) ∈ intAE D :=
    not_not.1 ((he.2 _ hN0).not.1 hNw)
  have hNE : (((N : 𝓞 D.host.E) : D.host.E)) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : (N : AE D) * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹ = 1 := by
    rw [show (N : AE D) = incA D (((N : 𝓞 D.host.E) : D.host.E)) by simp, ← map_mul, mul_inv_cancel₀ hNE, map_one]
  have key : (x : AE D) - 1 = (N : AE D) * (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹ * ((x : AE D) - 1)) := by
    linear_combination (-1 : AE D) * hx - (e * ((x : AE D) - 1)) * hi
  refine hN1 x ⟨?_, h1, h2⟩ ⟨finPart D (e * incA D (((N : 𝓞 D.host.E) : D.host.E))⁻¹) * (finPart D (x : AE D) - 1),
    intAE_mul hg (sub_mem h1 intAE_one), ?_⟩
  · have h0 := infPart_idem he.1
    have := congrArg (infPart D) hx
    simp only [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h0, zero_mul, zero_add, sub_zero] at this
    exact this.symm
  · have := congrArg (finPart D) key
    simp only [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, map_natCast] at this
    rw [nsmul_eq_mul]
    refine this.trans ?_
    simp only [RingHom.map_mul, map_natCast]

end GlobalTheory.UnrOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralEqOfLineBundleIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem chernInt_indep_of_iso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) A), LBIso L A → φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := by
  intro Y L A φ ψ hLA hφ hψ
  obtain ⟨w, hw⟩ := hLA
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.ChernIso.chernMass_ofIso Y L A φ ψ.isLB w hw hφ
  rw [← h2]
  exact _root_.GlobalTheory.ChernMass.chernInt_one_eq Y A _ ψ h1 hψ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormsOf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ColNorms

theorem errUnit_nonneg (N : NumDatum) {T : ℕ} (hT : 1 ≤ T) : 0 ≤ errUnit N T := by
  have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
  have h1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
  have h2 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h3 : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1) h2)
  unfold errUnit
  positivity

theorem kernelBound_ge (N : NumDatum) (δ : Code N) (T : ℕ) (C₁ C₂ : ℝ) (j : ℕ) (lo : RPl N.R → ℝ) (lt : ℝ) (h h' n n' : ℕ) :
    kernelBound_sq N δ T C₁ j lo lt 1 1 1 1 + 2 * (C₂ * errUnit N T) ≤ kernelBound_sq N δ T (C₁ + C₂) j lo lt h h' n n' := by
  have a1 : 0 ≤ Real.log ((h : ℝ) * h') := by exact_mod_cast Real.log_natCast_nonneg (h * h')
  have a2 : 0 ≤ Real.log ((n : ℝ) * n') := by exact_mod_cast Real.log_natCast_nonneg (n * n')
  unfold kernelBound_sq errUnit
  simp only [Nat.cast_one, mul_one, Real.log_one]
  nlinarith

theorem SmallDatum.mono {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    {S : Finset (HeightOneSpectrum (𝓞 E))} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {c : ℕ}
    {Ξ : HomE E a b → K} {β β' : ℝ} (h : SmallDatum S N N' c Ξ β) (hβ : β ≤ β') : SmallDatum S N N' c Ξ β' :=
  ⟨h.1, h.2.1, fun σ x => (h.2.2 σ x).trans hβ⟩

end GlobalTheory.ColNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryLocalComponentToLocalUnitaryGroStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryLocalComponent_toLocalUnitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ w : Pl E, Continuous (fun x : finU (E := E) (n := n) => toSub (UL n w) (cLoc w (x : UA E n))) := by
  first | exact @GlobalTheory.BCT.toSub_cLoc_fin_continuous | exact GlobalTheory.BCT.toSub_cLoc_fin_continuous | (intros; apply GlobalTheory.BCT.toSub_cLoc_fin_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutPMulCutP
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CentreFin

variable {n r : ℕ}

variable {J : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin r) ℂ}

theorem dual_swap (hJ : Jᴴ = J) (hxy : Xᴴ * J * Y = 1) : Yᴴ * J * X = 1 := by
  have := congrArg conjTranspose hxy
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, conjTranspose_one, ← Matrix.mul_assoc] at this

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem map_cT_emb (h : IsCMExt F E σ) (τ : E →+* ℂ) {a b : ℕ} (C : Matrix (Fin a) (Fin b) E) :
    (Formalism.UG.cT (σ : E →+* E) C).map τ = (C.map τ)ᴴ :=
  Matrix.ext fun i j => h.2.2.2 τ (C j i)

theorem frame_emb (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (τ : E →+* ℂ) :
    (X.map τ)ᴴ * J.map τ * X.map τ = 0 ∧ (Y.map τ)ᴴ * J.map τ * Y.map τ = 0 ∧ (X.map τ)ᴴ * J.map τ * Y.map τ = 1 := by
  simp only [← map_cT_emb h, ← Matrix.map_mul]
  rw [hW.xx, hW.yy, hW.xy]
  exact ⟨Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)⟩

end Global

end GlobalTheory.CentreFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCaseStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case : GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernDegree := by
  first | exact @GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | exact GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | (intros; apply GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex <;> assumption)
end

