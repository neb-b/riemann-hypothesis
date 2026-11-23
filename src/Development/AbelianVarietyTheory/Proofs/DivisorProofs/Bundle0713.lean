module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0002
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import GroundTheory.AutomorphicForms.ReductionCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0706
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMember
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg.MinSecond

section Transport

variable {p q : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isHW_equiv (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (μ : Ix p q → ℚ) (v : V) (hv : IsHW a μ v) : IsHW b μ (e v) := by
  obtain ⟨h0, h1⟩ := hv
  refine ⟨fun h' => h0 (e.map_eq_zero_iff.mp h'), ?_⟩
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 ⊢
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [← h, ← map_smul, ← map_sub, h1.1 i, map_zero]
  · rw [← h, h1.2 i j hij, map_zero]

theorem symm_equivariant (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v)) (Z : Mat p q) (w : W) :
    e.symm (b Z w) = a Z (e.symm w) := by
  apply e.injective
  rw [h, e.apply_symm_apply, e.apply_symm_apply]

theorem ofType_equiv (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (μ : Ix p q → ℚ) (v : V) (hv : OfType a μ v) : OfType b μ (e v) := by
  obtain ⟨U, hf, hvU, hst, hw⟩ := hv
  refine ⟨U.map (e : V →ₗ[ℂ] W), inferInstance, ⟨v, hvU, rfl⟩, ?_, ?_⟩
  · rintro X hX _ ⟨u, hu, rfl⟩
    exact ⟨a X u, hst X hX u hu, h X u⟩
  · rintro ν _ ⟨u, hu, rfl⟩ hν
    refine hw ν u hu ?_
    have := isHW_equiv e.symm b a (symm_equivariant e a b h) ν _ hν
    simpa using this

theorem genSub_map (e : V →ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (S : Set V) (T : Set W) (hST : ∀ v ∈ S, e v ∈ T) (v : V) (hv : v ∈ genSub a S) :
    e v ∈ genSub b T := by
  simp only [genSub, Submodule.mem_sInf, Set.mem_ofPred_eq] at hv ⊢
  intro N hN
  refine hv (N.comap e) ⟨fun x hx => hN.1 (hST x hx), fun Z y hy => ?_⟩
  rw [Submodule.mem_comap, h]
  exact hN.2 Z _ hy

end Transport

noncomputable def swapPol (p q r s : ℕ) : Pol p q r s ≃ₗ[ℂ] Pol r s p q :=
  (renameEquiv ℂ (Equiv.prodComm (Ix p q) (Ix r s))).toLinearEquiv

end GlobalTheory.FockAlg.MinSecond


open GlobalTheory.FockAlg.MinSecond in
theorem GlobalTheory.FockAlg.min_second : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M2 → AdmGK M2 → Intw M1 M2 f → f ≠ 0 → ∀ (μ' : Ix r s → ℚ), (∃ v, IsHW M2.act μ' v) → (∀ ν w, IsHW M2.act ν w → degW (cPair p q) μ' ≤ degW (cPair p q) ν) → (∃ (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct2 p q r s) μ' P → f P ∈ Submodule.map f (genSub (fockAct1 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}) := by
  intro p q r s M1 M2 f hirr hadm hf hf0 μ' hμ hmin
  obtain ⟨s1, s2, s3⟩ := _root_.GlobalTheory.FockSwap.swap_symmetry r s p q
  set e := swapPol r s p q with he
  have h1 : ∀ Z v, e (fockAct1 r s p q Z v) = fockAct2 p q r s Z (e v) := s1
  have h2 : ∀ Z v, e (fockAct2 r s p q Z v) = fockAct1 p q r s Z (e v) := s2
  have hJ : ∀ P, P ∈ jointHarm r s p q → e P ∈ jointHarm p q r s := fun P hP =>
    ⟨(s3 P).1.mp hP.2, (s3 P).2.mp hP.1⟩
  set c := TensorProduct.comm ℂ M1.V M2.V with hc
  let g : Pol r s p q →ₗ[ℂ] TensorProduct ℂ M2.V M1.V :=
    (c : _ →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e : _ →ₗ[ℂ] _)
  have hg : ∀ P, g P = c (f (e P)) := fun _ => rfl
  have hcm : ∀ (A : Module.End ℂ M1.V) (B : Module.End ℂ M2.V) x,
      c (TensorProduct.map A B x) = TensorProduct.map B A (c x) := by
    intro A B x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hc]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hgI : Intw M2 M1 g := by
    refine ⟨fun X => LinearMap.ext fun P => ?_, fun X => LinearMap.ext fun P => ?_⟩
    · have := LinearMap.congr_fun (hf.2 X) (e P)
      simp only [LinearMap.comp_apply] at this ⊢
      rw [hg, hg, h1, this, hcm]
    · have := LinearMap.congr_fun (hf.1 X) (e P)
      simp only [LinearMap.comp_apply] at this ⊢
      rw [hg, hg, h2, this, hcm]
  have hg0 : g ≠ 0 := by
    intro h
    apply hf0
    refine LinearMap.ext fun P => ?_
    have := LinearMap.congr_fun h (e.symm P)
    rw [hg, e.apply_symm_apply, LinearMap.zero_apply] at this
    exact c.map_eq_zero_iff.mp this
  obtain ⟨⟨μ, P, hP, hP1, hP2, hP0⟩, hB⟩ := _root_.GlobalTheory.FockAlg.min_first r s p q M2 M1 g hirr hadm hgI hg0 μ' hμ hmin
  refine ⟨⟨μ, e P, hJ P hP, isHW_equiv e _ _ h2 _ _ hP2, isHW_equiv e _ _ h1 _ _ hP1, ?_⟩, ?_⟩
  · intro h
    apply hP0
    rw [hg, h, map_zero]
  · intro R hR
    obtain ⟨Q, hQ, hQe⟩ := hB (e.symm R)
      (ofType_equiv e.symm _ _ (symm_equivariant e _ _ h1) _ _ hR)
    refine ⟨e Q, ?_, ?_⟩
    · exact genSub_map e.toLinearMap (fockAct2 r s p q) (fockAct1 p q r s) h2
        {Q | Q ∈ jointHarm r s p q ∧ OfType (fockAct1 r s p q) μ' Q}
        {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}
        (fun v hv => ⟨hJ v hv.1, ofType_equiv e _ _ h1 _ _ hv.2⟩) Q hQ
    · rw [hg, hg, e.apply_symm_apply] at hQe
      exact c.injective hQe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMassUpperBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open Formalism.MainNotions.StandardLattice (stdForm stdLat)
open Formalism.HermitianLatticesTheory (gmap isom genus)

namespace GlobalTheory

namespace StdMassBound

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

noncomputable def matEquiv (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    (Fin n → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin γ) (Matrix.mulVecLin γ.conjTranspose)
    (by rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, mul_eq_one_comm.1 h, Matrix.mulVecLin_one])

theorem matEquiv_mem (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    matEquiv γ h ∈ isom (stdForm E n) := by
  intro x y
  change star (γ.mulVec x) ⬝ᵥ (γ.mulVec y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, mul_eq_one_comm.1 h, Matrix.one_mulVec]

theorem diagForm_eq : Examples₂.diagForm (E := E) n (fun _ => false) = stdForm E n := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  change ∑ i, star (x i) * Examples₂.sgn false * y i = ∑ i, star (x i) * y i
  simp [Examples₂.sgn]

variable [NumberField E]

omit [StarRing E] in
theorem stdLat_eq : Examples₂.stdLat (E := E) n = stdLat E n := by
  unfold Examples₂.stdLat stdLat
  congr 2
  funext i
  exact Pi.basisFun_apply E (Fin n) i

omit [StarRing E] in
theorem mem_one_iff (a : E) : a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨r, rfl⟩
    exact r.isIntegral_coe
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

theorem selfDual_of_mem_genus {M : Submodule (𝓞 E) (Fin n → E)} (hM : M ∈ genus (stdForm E n) (stdLat E n))
    (y : Fin n → E) : y ∈ M ↔ ∀ x ∈ M, IsIntegral ℤ (∑ i, star (x i) * y i) := by
  have hsym : (stdForm E n).IsSymm := diagForm_eq (E := E) (n := n) ▸ Examples₂.diagForm_isSymm n _
  obtain ⟨-, -, hinv⟩ := Formalism.HermitianLatticesTheory.genusBasic (𝓞 E) E (Fin n → E) (stdForm E n) hsym
    (Examples₂.star_integral Examples₂.star_isIntegral)
  have h0 : Formalism.HermitianLatticesTheory.IsUnimodular (stdForm E n) (stdLat E n) := by
    rw [← diagForm_eq, ← stdLat_eq]
    exact Examples₂.stdLat_unimod Examples₂.star_isIntegral n _
  have hfg : (stdLat E n).FG := Submodule.fg_span (Set.finite_range _)
  have hu : Formalism.HermitianLatticesTheory.dual (stdForm E n) M = M := ((hinv _ _ hfg hM.1.fg hM.2).1).1 h0
  conv_lhs => rw [← hu]
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, mem_one_iff]
  rfl

end StdMassBound


open StdMassBound in
theorem mass_stdLat_le :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E],
    (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ,
    Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) ≤
      (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ E * n ^ 2) := by
  intro E _ _ _ _ hs n
  have hexists : ∃ R : Finset (Submodule (𝓞 E) (Fin n → E)),
      (R.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG →
        (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i)) →
        ∃ L₀ ∈ R, ∃ γ : Matrix (Fin n) (Fin n) E,
          γ * (γ.map (IsCMField.complexConj E)).transpose = 1 ∧
          ∀ x, x ∈ L₀ ↔ γ.mulVec x ∈ L := by
    open RootClassCount ReciprocityTheory.ChartRestriction.G.FD in
    obtain ⟨R, -, h2, h3⟩ := ClassCount.exists_finset_classes (K := E) (r := n) (G := 1)
      {L | L.FG ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (herm 1 y x)}
      (B := 4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2) (by positivity) fun L hL =>
        ⟨by simp, fun x hx => (hL.2 x).1 hx,
          exists_bounded_basis L hL.1 (fun x hx => (hL.2 x).1 hx) fun x hx => (hL.2 x).2 hx⟩
    refine ⟨R, h3.trans ?_, fun L hfg hsd => ?_⟩
    · have h := bound_le (fdeg E) n ClassCount.fdeg_pos (one_le_rootDiscr (E := E))
      rw [← ShortVectors.finrank_eq] at h
      rw [rdE_eq, ← ShortVectors.finrank_eq]
      exact h
    · obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := h2 L ⟨hfg, fun y => by
        simp only [isIntegral_herm_iff]; exact hsd y⟩
      exact ⟨L₀, hL₀, γ, mul_conjTranspose_eq_one _ hγ, hm⟩
  obtain ⟨R, hR, H⟩ := hexists
  refine le_trans ?_ hR
  unfold Formalism.HermitianLatticesTheory.mass
  split_ifs with hex
  swap
  · positivity
  obtain ⟨h1, h2⟩ := hex.choose_spec
  generalize hex.choose = s at h1 h2
  have key : ∀ M ∈ s, ∃ L₀ ∈ R, ∃ g ∈ isom (stdForm E n), gmap g L₀ = M := by
    intro M hM
    obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := H M (h1 M hM).1.fg (fun y => by
      simpa only [hs] using selfDual_of_mem_genus (h1 M hM) y)
    have hγ' : γ * γ.conjTranspose = 1 := by
      rw [← hγ]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply, hs]
    refine ⟨L₀, hL₀, matEquiv γ hγ', matEquiv_mem γ hγ', ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := (matEquiv γ hγ').surjective x
    constructor
    · rintro ⟨z, hz, e⟩
      rw [← e]
      exact (hm z).1 hz
    · intro hx
      exact ⟨x, (hm x).2 hx, rfl⟩
  choose! f hf g hg hfg using key
  have hcard : s.card ≤ R.card := by
    refine Finset.card_le_card_of_injOn f (fun M hM => hf M hM) fun M hM N hN e => ?_
    have hM' : M ∈ s := hM
    have hN' : N ∈ s := hN
    refine (h2 M (h1 M hM')).unique ⟨hM', 1, one_mem _, Formalism.HermitianLatticesTheory.genusBasic_gmap_one _⟩
      ⟨hN', g M * (g N)⁻¹, mul_mem (hg M hM') (inv_mem (hg N hN')), ?_⟩
    have e1 : gmap (g N)⁻¹ N = f N := by
      conv_lhs => rw [← hfg N hN']
      rw [hfg N hN']
      have := Formalism.HermitianLatticesTheory.genusBasic_gmap_inv (g N) (f N)
      rwa [hfg N hN'] at this
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, e1, ← e, hfg M hM']
  calc ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm E n) M) : ℕ) : ℝ)⁻¹ ≤ ∑ M ∈ s, (1 : ℝ) :=
        Finset.sum_le_sum fun M _ => Nat.cast_inv_le_one _
    _ = s.card := by simp
    _ ≤ R.card := by exact_mod_cast hcard

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainUnipotent
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

theorem constTerm_unip_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ f : GA E a → ℂ, (∀ γ g, f (ratGL E a γ * g) = f g) → ∀ (y : BlockIx a r → Ad E) (g : GA E a), ∫ x in 𝓕, f (unip x * (unip y * g)) ∂μ = ∫ x in 𝓕, f (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hμ h𝓕 f hf y g
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  set h : (BlockIx a r → Ad E) → ℂ := fun x => f (unip x * g) with hh
  have hinv : ∀ (γ : ratN E a r) (x : BlockIx a r → Ad E), h (γ +ᵥ x) = h x := by
    rintro ⟨_, e, rfl⟩ x
    change f (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * g) = f (unip x * g)
    rw [unip_add, unip_algebraMap, mul_assoc, hf]
  have hL : ∀ x, f (unip x * (unip y * g)) = h (x + y) := fun x => by
    simp only [hh, unip_add, mul_assoc]
  simp_rw [hL]

  have hmp : MeasurePreserving (fun x : BlockIx a r → Ad E => x + y) μ μ := measurePreserving_add_right μ y
  have hemb : MeasurableEmbedding (fun x : BlockIx a r → Ad E => x + y) :=
    (MeasurableEquiv.addRight y).measurableEmbedding
  let S : Set (BlockIx a r → Ad E) := (fun x => x - y) ⁻¹' 𝓕
  have hpre : (fun x : BlockIx a r → Ad E => x + y) ⁻¹' S = 𝓕 := by
    ext x; simp [S]
  have hS : IsAddFundamentalDomain (ratN E a r) S μ := by
    refine h𝓕.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · exact (measurePreserving_sub_right μ y).quasiMeasurePreserving
    · intro γ x
      change (γ : BlockIx a r → Ad E) + x - y = (γ : BlockIx a r → Ad E) + (x - y)
      abel
  calc ∫ x in 𝓕, h (x + y) ∂μ = ∫ x in (fun x : BlockIx a r → Ad E => x + y) ⁻¹' S, h (x + y) ∂μ := by rw [hpre]
    _ = ∫ x in S, h x ∂μ := hmp.setIntegral_preimage_emb hemb h S
    _ = ∫ x in 𝓕, h x ∂μ := hS.setIntegral_eq h𝓕 hinv

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrationOverCyclesLiftsLieLattice
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem pLie_holds : PLie := by
  intro A _ g hA _ L u P hP x
  have hs := _root_.GlobalTheory.abelianScheme_left_isSeparated_of_affine A hA
  obtain ⟨K, -, -, hK, hsm, -⟩ := GlobalTheory.T.exists_small_chart_pair_along_linear_map (fibUnif u) (fibUnif u) id analyticOnNhd_id (fun _ h ↦ h)
    LinearMap.id (AddMonoidHom.id _) (fun _ _ _ ↦ rfl)
  obtain ⟨r, hr, -⟩ := _root_.GlobalTheory.AnPer.exists_real_isFor (fibUnif u) hs K hsm
  obtain ⟨k, hk⟩ := hK.1 0 trivial
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.AnPer.Hol.exists_jet_algHom (K.W k) 0 hk (0, (x : Fin g → ℂ))
  obtain ⟨v, hv, ht, hd⟩ := _root_.GlobalTheory.AnPer.exists_tangent_of_jet u hs (K.W k) (r.x k) (hr k)
    ((congrArg (r.x k ≫ ·) (Category.comp_id A.hom).symm).trans (r.w k)) hk x ρ hρ
  refine ⟨v, ⟨ht, fun f hf ↦ ?_⟩, hd⟩
  obtain ⟨q, G, hq, hG, hGk, hGl⟩ := GlobalTheory.T.exists_global_bound_of_period_class K hK r f _ (hP ⟨_, hf⟩ K r hr)
  rw [GlobalTheory.T.form_on_tangent_eq_derivative_bounding_function K r k 0 hk x ρ hρ v hv f _ q hq, Hol.fderiv_fn_congr _ (hGk k) hk]
  have hdG : ∀ p, DifferentiableAt ℂ G p := fun p ↦ (hG p trivial).differentiableAt
  have hi : ∀ w : Fin g → ℂ, HasFDerivAt (fun w : Fin g → ℂ ↦ ((0, w) : Tot Empty g))
      (ContinuousLinearMap.inr ℂ (Empty → ℂ) (Fin g → ℂ)) w := fun w ↦ hasFDerivAt_prodMk_right _ _
  have := GlobalTheory.fderiv_zero_eq_of_const_differences u.Λ u.full (fun w ↦ G (0, w)) (fun l ↦ P l ⟨_, hf⟩)
    (fun w ↦ (hdG _).comp w (hi w).differentiableAt)
    (fun l w ↦ (hGl l (0, w) trivial).trans (congrArg (G (0, w) + ·) (Hol.fn_algebraMap _ trivial))) x
  rw [← this]
  exact congrArg (fun D : (Fin g → ℂ) →L[ℂ] ℂ ↦ D x) ((hdG (0, 0)).hasFDerivAt.comp (0 : Fin g → ℂ) (hi 0)).fderiv

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentConstEqOfTendsto
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.ThetaInner
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

theorem laurentConst_eq_of_tendsto :
    ∀ (h : ℂ → ℂ) (s₀ c c' : ℂ), LaurentConst h s₀ c → Tendsto h (𝓝[≠] s₀) (𝓝 c') → c = c' := by
  rintro h s₀ c c' ⟨p, hp0, hp⟩ hh
  have h1 : Tendsto (fun s : ℂ => p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 (c' - c)) := by
    refine (hh.sub hp).congr fun s => ?_
    ring
  have h2 : Tendsto (fun s : ℂ => s - s₀) (𝓝[≠] s₀) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℂ => s - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
        (continuous_id.sub continuous_const).tendsto s₀
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_ne_zero.2 hs
  have h3 : Tendsto (fun s : ℂ => ‖(s - s₀)⁻¹‖) (𝓝[≠] s₀) atTop :=
    tendsto_norm_cobounded_atTop.comp (tendsto_inv₀_nhdsNE_zero.comp h2)
  by_cases hd : 0 < p.degree
  · exact absurd (p.tendsto_norm_atTop hd h3) (not_tendsto_atTop_of_tendsto_nhds h1.norm)
  · have hp' : p = 0 := by
      rw [Polynomial.eq_C_of_degree_le_zero (not_lt.1 hd), hp0, map_zero]
    subst hp'
    simp only [Polynomial.eval_zero, sub_zero] at hp
    exact tendsto_nhds_unique hp hh

end GlobalTheory.ThetaInner
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
section
open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

theorem Zalg_mul_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a)
    (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a →
      z * GlobalTheory.CuspRep.lie E a X = GlobalTheory.CuspRep.lie E a X * z := by
  intro E _ _ _ a X z hz
  have h : GlobalTheory.CuspRep.Zalg E a ≤ Subalgebra.centralizer ℂ {GlobalTheory.CuspRep.lie E a X} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (commute_cap_lie τ u X).eq.symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (h hz) _ rfl).symm

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCF

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def absDetA (g : GA E a) : ℝ :=
  GroundTheory.Automorphic.Reduction.adeleAbs ((Matrix.GeneralLinearGroup.det g : (Ad E)ˣ) : Ad E)

theorem absDetA_pos (g : GA E a) : 0 < absDetA g := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) (Matrix.GeneralLinearGroup.det g)]
  exact ((GroundTheory.Global.IdeleGroup.ideleModule E) (Matrix.GeneralLinearGroup.det g)).2

theorem absDetA_one : absDetA (1 : GA E a) = 1 := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) (Matrix.GeneralLinearGroup.det (1 : GA E a)), map_one, map_one]
  rfl


variable (E a) in
def band : Set (GA E a) := {g | 1 ≤ absDetA g ∧ absDetA g ≤ 2}

theorem one_mem_band : (1 : GA E a) ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, absDetA_one]; norm_num

end GlobalTheory.HCF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorsCMFieldOfSiegelKlingenDelStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators := by
  first | exact @GlobalTheory.ZetaDenom.zetaDenominators | exact GlobalTheory.ZetaDenom.zetaDenominators | (intros; apply GlobalTheory.ZetaDenom.zetaDenominators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftKillsCuspDivisibleDegree
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_lift_kills_cusp_divisible_degree : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n) := by
  first | (exact @GlobalTheory.Shin.shLift_cusp_kills_J) | (exact GlobalTheory.Shin.shLift_cusp_kills_J) | (intros; apply GlobalTheory.Shin.shLift_cusp_kills_J  <;> assumption)
end

