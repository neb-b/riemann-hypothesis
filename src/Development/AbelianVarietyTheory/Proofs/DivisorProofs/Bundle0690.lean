module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0673
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveOfLocalBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieProj

theorem finite_projective_of_localBasis : ∀ {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ),
    (∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal,
      Nonempty (Module.Basis (Fin n) (Localization.Away r) (LocalizedModule (Submonoid.powers r) M))) →
    Module.Finite R M ∧ Module.Projective R M ∧ ∀ p, Module.rankAtStalk (R := R) M p = n := by
  intro R M _ _ _ n h
  let t : Set R := {r | Nonempty (Module.Basis (Fin n) (Localization.Away r)
    (LocalizedModule (Submonoid.powers r) M))}
  have ht : Ideal.span t = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hb⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hle (Ideal.subset_span hb))
  have hfree : ∀ g : t, Module.Free (Localization.Away g.1) (LocalizedModule (Submonoid.powers g.1) M) :=
    fun g => Module.Free.of_basis g.2.some
  have hfp : ∀ g : t, Module.FinitePresentation (Localization.Away g.1)
      (LocalizedModule (Submonoid.powers g.1) M) := fun g => by
    haveI := hfree g
    haveI : Module.Finite (Localization.Away g.1) (LocalizedModule (Submonoid.powers g.1) M) :=
      Module.Finite.of_basis g.2.some
    exact Module.finitePresentation_of_projective _ _
  haveI : Module.FinitePresentation R M := Module.FinitePresentation.of_localizationSpan t ht hfp
  haveI : Module.Flat R M := by
    refine Module.flat_of_localized_span R M t ht ?_
    intro g
    haveI := hfree g
    haveI : Module.Flat R (Localization.Away g.1) := IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) _
  refine ⟨inferInstance, Module.Flat.projective_of_finitePresentation, fun p => ?_⟩
  obtain ⟨r, hr, ⟨b⟩⟩ := h p
  have hq : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨q, rfl⟩ := hq
  haveI := Module.Free.of_basis b
  haveI : Nontrivial (Localization.Away r) := q.nontrivial
  rw [← Module.rankAtStalk_isBaseChange
    (LocalizedModule.isBaseChange (Submonoid.powers r) M) q,
    Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank (Localization.Away r) (LocalizedModule (Submonoid.powers r) M) = n
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

theorem exists_chart_lieBasis : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ),
    SmoothOfRelativeDimension n G.hom → ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal,
      Nonempty (ReciprocityTheory.ChartRestriction.G.Chart.Chart (ReciprocityTheory.ChartRestriction.G.Chart.Gs G r)) ∧
      ∃ v : Fin n → (epsR (Localization.Away r) ⟶ ReciprocityTheory.ChartRestriction.G.Chart.Gs G r), IsLieBasis v := by
  intro R _ G _ _ n h p
  let e : Spec (CommRingCat.of R) ⟶ G.left := η[G].left
  obtain ⟨S, _, _, j, hS, hj, hmem⟩ := GlobalTheory.LieLoc.exists_standardSmooth_chart G n h (e p)
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := (e ⁻¹ᵁ j.left.opensRange).1) hmem (e ⁻¹ᵁ j.left.opensRange).2
  refine ⟨r, hr, ReciprocityTheory.ChartRestriction.G.Chart.chart_away G j.left.opensRange (by haveI : IsAffine (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) S).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of S))); exact isAffineOpen_opensRange j.left) r
    (fun x hx => hsub (show x ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) from hx)), ?_⟩
  obtain ⟨ε, hε⟩ := GlobalTheory.SqZero.exists_chart_pt j
    (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (Localization.Away r) ⟶ G) (by
    rintro _ ⟨t, rfl⟩
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) t ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨t, rfl⟩
    exact hsub this)
  obtain ⟨x, hx⟩ := GlobalTheory.LieLoc.univChart_baseChange G n S j _ ε hε.symm
  exact ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.basis_of_chart hx⟩

end GlobalTheory.LieProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionHomogeneousEigenvector
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.JointHarm

namespace GlobalTheory.FockScalarType

theorem injective_of_isFockIP {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι) :
    Function.Injective ι := by
  have key : ∀ (α : σ →₀ ℕ) (P : MvPolynomial σ ℂ), inner ℂ (ι (monomial α 1)) (ι P) =
      AddMonoidAlgebra.coeff P α * α.prod (fun _ k => (k.factorial : ℂ)) := by
    intro α P
    induction P using MvPolynomial.induction_on' with
    | add P P' h h' => simp only [map_add (f := _), inner_add_right, h, h', MvPolynomial.coeff_add, add_mul]
    | monomial β c =>
      rw [monomial_eq_smul β c, map_smul, inner_smul_right, hι, coeff_smul, coeff_monomial]
      by_cases e : α = β
      · subst e; simp
      · simp [e, Ne.symm e]
  refine (injective_iff_map_eq_zero ι).2 fun P hP => ?_
  ext α
  have h := key α P
  rw [hP, inner_zero_right, eq_comm, mul_eq_zero] at h
  refine h.resolve_right ?_
  exact Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

variable {p q r s : ℕ}

def charSub (p q r s : ℕ) (x : ℚ) : Submodule ℂ (Pol p q r s) where
  carrier := {f | ∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y f = ((x : ℂ) * Y.trace) • f}
  add_mem' := fun ha hb Y hY => by rw [map_add (f := _), ha Y hY, hb Y hY, smul_add]
  zero_mem' := fun Y _ => by simp
  smul_mem' := fun c _ ha Y hY => by rw [map_smul, ha Y hY, smul_comm]

theorem isKC_Eab {a b : Ix p q} (hab : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd hab

theorem isHW_of_mem {x : ℚ} {f : Pol p q r s} (h0 : f ≠ 0) (hf : f ∈ charSub p q r s x) :
    IsHW (fockAct1 p q r s) (fun _ => x) f := by
  refine ⟨h0, ?_, ?_⟩
  · simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    intro a
    rw [hf _ (isKC_Eab (by rcases a with a | a <;> trivial))]
    simp [Eab]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b hab
    have h1 : sameBlock a b := by
      rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]
    have h2 : a ≠ b := by
      rintro rfl
      rcases a with a | a <;> simp [posC] at hab
    rw [hf _ (isKC_Eab h1), Eab, Matrix.trace_single_eq_of_ne _ _ _ h2]
    simp

theorem comm_parts {Y : Mat p q} (hY : IsKC Y) {Z : Mat r s} (hZ : IsPC Z) {d : ℕ}
    {v : Pol p q r s} (hv : v ∈ homog (Ln p q r s) d) :
    fockAct1 p q r s Y (upOp (kron2 p q Z) v) = upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∧
    fockAct1 p q r s Y (dnOp (kron2 p q Z) v) = dnOp (kron2 p q Z) (fockAct1 p q r s Y v) := by
  have hK : ∀ {d : ℕ} {w : Pol p q r s}, w ∈ homog (Ln p q r s) d →
      fockAct1 p q r s Y w ∈ homog (Ln p q r s) d := fun hw =>
    GlobalTheory.FockDeg.omAct_mem_homog (GlobalTheory.FockDeg.lineMatrixKroneckerLeftFactor_eq_zero_of_isKC hY) hw
  have hc := LinearMap.congr_fun ((GlobalTheory.FockPair.pair_lie_commute p q r s).2.2 Y Z) v
  rw [Module.End.mul_apply, Module.End.mul_apply, fockAct2_eq, omAct_odd (odd_kron2 hZ),
    LinearMap.add_apply, LinearMap.add_apply, map_add] at hc
  have h1 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∈
      homog (Ln p q r s) (d + 2) :=
    Submodule.sub_mem _ (hK (upOp_homog _ d v hv)) (upOp_homog _ d _ (hK hv))
  have h2 : dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) ∈
      homog (Ln p q r s) (d - 2) :=
    Submodule.sub_mem _ (dnOp_homog _ d _ (hK hv)) (hK (dnOp_homog _ d v hv))
  have e : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) =
      dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) := by
    linear_combination hc
  have h0 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) -
      upOp (kron2 p q Z) (fockAct1 p q r s Y v) = 0 := by
    by_contra hne
    have := IsHomogeneous.inj_right h1 (e ▸ h2) hne
    omega
  exact ⟨sub_eq_zero.1 h0, (sub_eq_zero.1 (e ▸ h0)).symm⟩

theorem upOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    upOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).1, hc Y hY, map_smul]

theorem dnOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    dnOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).2, hc Y hY, map_smul]

theorem eq_zero_of_lowering {x : ℚ} {e e₀ : ℕ} {g v : Pol p q r s} (hg0 : g ≠ 0)
    (hg : g ∈ homog (Ln p q r s) e₀) (hgc : g ∈ charSub p q r s x) (he : e₀ < e)
    (hv : v ∈ homog (Ln p q r s) e) (hvc : v ∈ charSub p q r s x)
    (hd : ∀ Z : Mat r s, IsPC Z → dnOp (kron2 p q Z) v = 0) : v = 0 := by
  by_contra h0
  have h1 := isSide_one.degW_le Function.bijective_id hg (isHW_of_mem hg0 hgc)
  obtain ⟨d, hd1, hd2⟩ := isSide_one.homog_of_hw Function.bijective_id (isHW_of_mem h0 hvc)
    ((mem_harm1 v).1 fun Z hZ => by
      rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) v).2, hd Z hZ])
  obtain rfl : d = e := IsHomogeneous.inj_right hd2 hv h0
  rw [← hd1, Nat.cast_le] at h1
  omega

theorem mem_span_raising : ∀ (P Q R S : ℕ) (x : ℚ) (e e₀ : ℕ) (f g : Pol P Q R S),
    f ∈ homog (Ln P Q R S) e →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y f = ((x : ℂ) * Y.trace) • f) →
    g ≠ 0 → g ∈ homog (Ln P Q R S) e₀ →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g = ((x : ℂ) * Y.trace) • g) →
    e₀ < e →
    f ∈ Submodule.span ℂ {f' | ∃ Z : Mat R S, IsPC Z ∧
      ∃ g' ∈ homog (Ln P Q R S) (e - 2),
        (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 P Q R S Z) g'} := by
  intro p q r s x e e₀ f g hf hfc hg0 hg hgc he
  by_cases h2 : e < 2
  · rw [eq_zero_of_lowering hg0 hg hgc he hf hfc fun Z _ => dnOp_low _ e h2 f hf]
    exact Submodule.zero_mem _
  have hι := GlobalTheory.FockAlg.Model.isFockIsometry_fockEmb (Ln p q r s)
  have hinj := injective_of_isFockIP hι
  set U := Submodule.span ℂ {f' | ∃ Z : Mat r s, IsPC Z ∧
      ∃ g' ∈ homog (Ln p q r s) (e - 2),
        (∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 p q r s Z) g'} with hU
  have hle : U ≤ homog (Ln p q r s) e ⊓ charSub p q r s x := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, hZ, g', h1, h3, rfl⟩
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) g').1]
    refine ⟨?_, upOp_mem_charSub hZ h1 h3⟩
    have := upOp_homog (kron2 p q Z) _ g' h1
    rwa [show e - 2 + 2 = e by omega] at this
  have := Submodule.finiteDimensional_of_le (hle.trans inf_le_left)
  obtain ⟨u, hu, ho⟩ := exists_orth (GlobalTheory.FockAlg.Model.fockEmb (Ln p q r s)) U f
  have hh := Submodule.sub_mem _ hf (hle hu).1
  have hc : f - u ∈ charSub p q r s x := Submodule.sub_mem _ hfc (hle hu).2
  have h0 : f - u = 0 := eq_zero_of_lowering hg0 hg hgc he hh hc fun Z hZ => by
    have hZ' := isPC_conjTranspose hZ
    have h1 := ho _ (Submodule.subset_span ⟨_, hZ', _, dnOp_homog (kron2 p q Z) e _ hh,
      dnOp_mem_charSub hZ hh hc, rfl⟩)
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ') _).1, inner_upOp hι (odd_kron2 hZ'),
      ← lineKroneckerRightMatrix_conjTranspose, neg_eq_zero, inner_self_eq_zero] at h1
    exact hinj (h1.trans (map_zero _).symm)
  rw [sub_eq_zero.1 h0]
  exact hu

end GlobalTheory.FockScalarType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjoints
section
noncomputable section
namespace GlobalTheory.FockAdj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.FockDeg MvPolynomial Matrix

variable {p q r s : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_pderiv {σ : Type} [DecidableEq σ] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι)
    (i : σ) (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (pderiv i P)) (ι Q) = inner ℂ (ι P) (ι (X i * Q)) := by
  rw [← inner_conj_symm, ← inner_X_mul hι, inner_conj_symm]

theorem inner_raiB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (raiB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (lowB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (-pderiv l P)) (ι Q) = -1 * inner ℂ (ι P) (ι (X l * Q))
    rw [map_neg, inner_neg_left, inner_pderiv hι, neg_one_mul]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (X l * P)) (ι Q) = 1 * inner ℂ (ι P) (ι (pderiv l Q))
    rw [inner_X_mul hι, one_mul]

theorem inner_lowB {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (lowB l P)) (ι Q) = (if linePos l then 1 else -1) * inner ℂ (ι P) (ι (raiB l Q)) := by
  cases hl : linePos l
  · simp only [raiB, lowB, hl, Bool.false_eq_true, if_false]
    show inner ℂ (ι (X l * P)) (ι Q) = -1 * inner ℂ (ι P) (ι (-pderiv l Q))
    rw [map_neg, inner_neg_right, inner_X_mul hι, neg_one_mul, neg_neg]
  · simp only [raiB, lowB, hl, if_true]
    show inner ℂ (ι (pderiv l P)) (ι Q) = 1 * inner ℂ (ι P) (ι (X l * Q))
    rw [inner_pderiv hι, one_mul]

theorem inner_omE {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (l l' : Ln p q r s)
    (P Q : Pol p q r s) :
    inner ℂ (ι (omE l l' P)) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (omE l' l Q)) := by
  have h1 : inner ℂ (ι (raiB l (lowB l' P))) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (raiB l' (lowB l Q))) := by
    rw [inner_raiB hι, inner_lowB hι, ← mul_assoc]
    congr 1
    cases linePos l <;> cases linePos l' <;> simp
  unfold omE
  simp only [LinearMap.add_apply, Module.End.mul_apply, map_add (f := _), inner_add_left, inner_add_right,
    mul_add, h1]
  congr 1
  by_cases h : l = l'
  · subst h
    simp [inner_smul_left, inner_smul_right, map_ofNat]
  · simp [h, Ne.symm h]

theorem inner_omAct {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι)
    (M N : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (h : ∀ l l', N l' l = (if linePos l = linePos l' then 1 else -1) * star (M l l'))
    (P Q : Pol p q r s) :
    inner ℂ (ι (omAct p q r s M P)) (ι Q) = inner ℂ (ι P) (ι (omAct p q r s N Q)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [inner_omE hι, h, starRingEnd_apply]
  ring

theorem adjZ_apply (Z : Mat p q) (a b : Ix p q) :
    adjZ Z a b = (if sameBlock b a then 1 else -1) * star (Z b a) := by
  have hJ : Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [adjZ, hJ, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [sameBlock]

theorem fock_adjoints : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι →
    (∀ (l l' : Ln p q r s) (P Q : Pol p q r s), inner ℂ (ι (omE l l' P)) (ι Q) =
      (if linePos l = linePos l' then 1 else -1) * inner ℂ (ι P) (ι (omE l' l Q))) ∧
    (∀ (Z : Mat p q) (P Q : Pol p q r s), inner ℂ (ι (fockAct1 p q r s Z P)) (ι Q) =
      inner ℂ (ι P) (ι (fockAct1 p q r s (adjZ Z) Q))) ∧
    (∀ (Z : Mat r s) (P Q : Pol p q r s), inner ℂ (ι (fockAct2 p q r s Z P)) (ι Q) =
      inner ℂ (ι P) (ι (fockAct2 p q r s (adjZ Z) Q))) := by
  intro p q r s H _ _ ι hι
  refine ⟨inner_omE hι, fun Z P Q => ?_, fun Z P Q => ?_⟩
  · rw [fockAct1_eq, fockAct1_eq]
    refine inner_omAct hι _ _ ?_ P Q
    rintro ⟨a, c⟩ ⟨b, d⟩
    by_cases e : c = d
    · subst e
      simp [kr1, adjZ_apply, linePos_eq_iff_fst]
    · simp [kr1, e, Ne.symm e]
  · rw [fockAct2_eq, fockAct2_eq]
    refine inner_omAct hι _ _ ?_ P Q
    rintro ⟨a, c⟩ ⟨b, d⟩
    by_cases e : a = b
    · subst e
      simp [kr2, adjZ_apply, linePos_eq_iff_snd]
    · simp [kr2, e, Ne.symm e]

end GlobalTheory.FockAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJointHarmonicsHighestWeightEqBotOfNotShape
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg

theorem jointHarm_hw_eq_bot : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    ¬ JointShape p q r s μ μ' →
      hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (jointHarm p q r s) = ⊥ :=
  fun _ _ _ _ μ μ' => (GlobalTheory.JointHarm.joint_harmonics μ μ').2

end GlobalTheory.FockAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOnTangentEqDerivativeBoundingFunctionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_on_tangent_eq_derivative_bounding_function : ∀ {A : Over (Sp ℂ)} {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol F.V))) (k : K.K) (p : Tot I g), p ∈ K.W k → ∀ (w : Fin g → ℂ) (ρ : Hol (K.W k) →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p (0, w)) → ∀ (v : epsR ℂ ⟶ A), v.left = spMap ρ.toRingHom ≫ r.x k → ∀ (f : Form (A.hom ≫ 𝟙 _)) (per : Λ →+ Hol F.V) (q : GlobalTheory.CatCoh.C0 K.Oc), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 → tanVal v f = fderiv ℂ (Hol.fn (W := K.W k) (q (K.triv k))) p (0, w) := by
  first | exact @GlobalTheory.AnPer.LieVal.main | exact GlobalTheory.AnPer.LieVal.main | (intros; apply GlobalTheory.AnPer.LieVal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitRootPolynomialFactorization
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel.RootPolyFactor

open GlobalTheory.GoodCharsCompare

theorem card_sigma_cyc {r : ℕ} (b : Fin r → Fin r) :
    Fintype.card (Σ c : Cyc b, Fin (cycLen b c)) = r := by
  have e : (Σ c : Cyc b, {i : Fin r // b i = c.1}) ≃ Fin r :=
    { toFun := fun y => y.2.1
      invFun := fun i => ⟨⟨b i, i, rfl⟩, i, rfl⟩
      left_inv := by
        rintro ⟨⟨c, hc⟩, i, hi⟩
        cases hi
        rfl
      right_inv := fun i => rfl }
  have := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_sigma] at this
  rw [Fintype.card_sigma]
  simpa using this

theorem rootsBar_prod {p : ℕ} [Fact p.Prime] {ι : Type} (s : Finset ι) (φ : ι → (ZMod p)[X])
    (h : ∀ c, (φ c).Monic) {z : Fbar p} :
    z ∈ Formalism.CyclotomicNorms.rootsBar (∏ c ∈ s, φ c) ↔ ∃ c ∈ s, z ∈ Formalism.CyclotomicNorms.rootsBar (φ c) := by
  rw [mem_rootsBar (monic_prod_of_monic _ _ fun c _ => h c).ne_zero, map_prod, Finset.prod_eq_zero_iff]
  simp only [mem_rootsBar (h _).ne_zero]

theorem dg_eq {p : ℕ} [Fact p.Prime] {r : ℕ} {b : Fin r → Fin r} {x : Cyc b → Fbar p}
    (hx : ∀ c, x c ^ (p ^ cycLen b c - 1) = 1) (hinj : Function.Injective (rootElt x)) (c : Cyc b) :
    dg (x c) = cycLen b c := by
  obtain ⟨k, hk⟩ := exists_dg_mul (cycLen_pos b c) (hx c)
  have h0 := cycLen_pos b c
  have hle : dg (x c) ≤ cycLen b c := Nat.le_of_dvd h0 ⟨k, hk⟩
  by_contra hne
  have hlt : dg (x c) < cycLen b c := lt_of_le_of_ne hle hne
  have := @hinj ⟨c, ⟨dg (x c), hlt⟩⟩ ⟨c, ⟨0, h0⟩⟩ (by
    show x c ^ p ^ dg (x c) = x c ^ p ^ 0
    rw [(frobenius_orbit_degreeOverPrimeFieldFbar (x c)).1, pow_zero, pow_one])
  have h2 := congrArg (fun y : (Σ c : Cyc b, Fin (cycLen b c)) => (y.2 : ℕ)) this
  exact (dg_pos (x c)).ne' h2

theorem mem_roots_lt {p : ℕ} [Fact p.Prime] {y z : Fbar p} :
    z ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) y) ↔ ∃ i < dg y, y ^ p ^ i = z := by
  classical
  rw [← Multiset.mem_toFinset, roots_minpoly]
  simp

theorem rootPoly_factor : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (b : Fin r → Fin r) (x : Cyc b → Fbar p) (f : (ZMod p)[X]), IsRootPoly x f → f.natDegree = r ∧ f.coeff 0 ≠ 0 ∧ (Squarefree f ↔ Function.Injective (rootElt x)) ∧ (Squarefree f → (∀ c, (minpoly (ZMod p) (x c)).natDegree = cycLen b c) ∧ Function.Injective (fun c => minpoly (ZMod p) (x c)) ∧ f = ∏ c, minpoly (ZMod p) (x c)) := by
  intro p _ r b x f ⟨hx, hm, hr⟩
  have hdeg : f.natDegree = r := by
    rw [← card_rootsBar, hr, Multiset.card_map, ← Finset.card_def, Finset.card_univ, card_sigma_cyc]
  have hsq : Squarefree f ↔ Function.Injective (rootElt x) := by
    rw [squarefree_iff hm.ne_zero, hr, Multiset.nodup_map_iff_inj_on Finset.univ.nodup]
    simp [Function.Injective]
  refine ⟨hdeg, ?_, hsq, fun hs => ?_⟩
  · rw [coeff_zero_iff hm.ne_zero, hr, Multiset.mem_map]
    rintro ⟨⟨c, i⟩, -, h⟩
    have h1 : x c = 0 := eq_zero_of_pow_eq_zero h
    have := hx c
    rw [h1, zero_pow (g_pow_sub_pos (cycLen_pos b c)).ne'] at this
    exact zero_ne_one this
  · have hinj := hsq.1 hs
    have hd := dg_eq hx hinj
    refine ⟨hd, fun c c' h => ?_, ?_⟩
    · have h1 : x c' ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) (x c)) := by
        rw [show minpoly (ZMod p) (x c) = minpoly (ZMod p) (x c') from h]
        exact mem_roots_minpoly.2 ⟨0, by simp⟩
      obtain ⟨i, hi, e⟩ := mem_roots_lt.1 h1
      have := @hinj ⟨c, ⟨i, hd c ▸ hi⟩⟩ ⟨c', ⟨0, cycLen_pos b c'⟩⟩ (by
        show x c ^ p ^ i = x c' ^ p ^ 0
        rw [e, pow_zero, pow_one])
      exact congrArg Sigma.fst this
    · have hmon : ∀ c, (minpoly (ZMod p) (x c)).Monic := fun c => minpoly.monic (isInt _)
      have hP := monic_prod_of_monic Finset.univ _ fun c _ => hmon c
      apply eq_of_rootsBar hm hP
      apply Multiset.eq_of_le_of_card_le
      · rw [Multiset.le_iff_subset ((squarefree_iff hm.ne_zero).1 hs)]
        intro z hz
        rw [hr, Multiset.mem_map] at hz
        obtain ⟨⟨c, i⟩, -, rfl⟩ := hz
        exact (rootsBar_prod _ _ hmon).2 ⟨c, Finset.mem_univ _, mem_roots_minpoly.2 ⟨i, rfl⟩⟩
      · rw [card_rootsBar, card_rootsBar, hdeg, natDegree_prod_of_monic _ _ fun c _ => hmon c]
        have := card_sigma_cyc b
        rw [Fintype.card_sigma] at this
        simp only [Fintype.card_fin] at this
        exact ((Finset.sum_congr rfl fun c _ => hd c).trans this).le

end GlobalTheory.ParamLabel.RootPolyFactor
end

