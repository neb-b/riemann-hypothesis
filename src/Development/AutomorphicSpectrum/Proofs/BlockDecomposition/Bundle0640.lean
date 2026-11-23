module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetClosedOpenSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIffFrameParabolic
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame.ParStab

section Linear

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def firstCols (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] : Matrix (ι ⊕ ι) ι R := Matrix.fromRows 1 0

theorem mul_firstCols (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) : g * firstCols R ι = g.toCols₁ := by
  ext r j
  simp [firstCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]

theorem firstCols_mul_apply_inl (m : Matrix ι ι R) (i j : ι) : (firstCols R ι * m) (Sum.inl i) j = m i j := by
  simp [firstCols, Matrix.mul_apply, Matrix.one_apply]

theorem firstCols_mul_apply_inr (m : Matrix ι ι R) (i j : ι) : (firstCols R ι * m) (Sum.inr i) j = 0 := by
  simp [firstCols, Matrix.mul_apply]

theorem firstCols_cancel {m m' : Matrix ι ι R} (h : firstCols R ι * m = firstCols R ι * m') : m = m' := by
  ext i j
  rw [← firstCols_mul_apply_inl m, h, firstCols_mul_apply_inl]

theorem low_zero_of_mul {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} {m : Matrix ι ι R} (h : g * firstCols R ι = firstCols R ι * m)
    (i j : ι) : g (Sum.inr i) (Sum.inl j) = 0 := by
  have := congrFun (congrFun h (Sum.inr i)) j
  rwa [mul_firstCols, firstCols_mul_apply_inr] at this

theorem mul_eq_of_low_zero {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (h : ∀ i j, g (Sum.inr i) (Sum.inl j) = 0) :
    g * firstCols R ι = firstCols R ι * g.toBlocks₁₁ := by
  ext r j
  rcases r with i | i
  · rw [firstCols_mul_apply_inl, mul_firstCols]; rfl
  · rw [firstCols_mul_apply_inr, mul_firstCols]; exact h i j

theorem mem_stab_iff (g : GL (ι ⊕ ι) R) : g ∈ stab R (Sum.inl '' (Set.univ : Set ι)) ↔
    ∀ i j, (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) (Sum.inl j) = 0 ∧
      ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) (Sum.inl j) = 0 := by
  constructor
  · intro h i j
    exact h (Sum.inr i) (by simp) (Sum.inl j) (by simp)
  · intro h r hr c hc
    obtain ⟨j, -, rfl⟩ := hc
    rcases r with i | i
    · exact absurd ⟨i, Set.mem_univ _, rfl⟩ hr
    · exact h i j

theorem exists_mul_eq_iff_mem_stab (B x : GL (ι ⊕ ι) R) (D : Matrix (ι ⊕ ι) ι R) (T : GL ι R)
    (hB : (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι = D * (T : Matrix ι ι R)) :
    (∃ t : GL ι R, (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * (t : Matrix ι ι R)) ↔
      B⁻¹ * x * B ∈ stab R (Sum.inl '' (Set.univ : Set ι)) := by
  have hBi : ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hTi : (T : Matrix ι ι R) * ((T⁻¹ : GL ι R) : Matrix ι ι R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hD : D = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
    rw [hB, Matrix.mul_assoc, hTi, Matrix.mul_one]
  have hC : ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (T : Matrix ι ι R) = firstCols R ι := by
    rw [Matrix.mul_assoc, ← hB, ← Matrix.mul_assoc, hBi, Matrix.one_mul]
  have hinv : (B⁻¹ * x * B)⁻¹ = B⁻¹ * x⁻¹ * B := by group
  have key : ∀ (g : GL (ι ⊕ ι) R) (s : Matrix ι ι R), (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * s →
      ((B⁻¹ * g * B : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι =
        firstCols R ι * (((T⁻¹ : GL ι R) : Matrix ι ι R) * s * (T : Matrix ι ι R)) := by
    intro g s hg
    calc _ = ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D) * (T : Matrix ι ι R) := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rw [hB]
      _ = ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (s * (T : Matrix ι ι R)) := by
          rw [hg]; simp only [Matrix.mul_assoc]
      _ = (((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (T : Matrix ι ι R)) *
            (((T⁻¹ : GL ι R) : Matrix ι ι R) * s * (T : Matrix ι ι R)) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (T : Matrix ι ι R) (((T⁻¹ : GL ι R) : Matrix ι ι R)), hTi, Matrix.one_mul]
      _ = _ := by rw [hC]
  constructor
  · rintro ⟨t, ht⟩
    have hx' : ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * ((t⁻¹ : GL ι R) : Matrix ι ι R) := by
      have h1 : ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 : (t : Matrix ι ι R) * ((t⁻¹ : GL ι R) : Matrix ι ι R) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc _ = ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (D * ((t : Matrix ι ι R) * ((t⁻¹ : GL ι R) : Matrix ι ι R))) := by
            rw [h2, Matrix.mul_one]
        _ = ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D) * ((t⁻¹ : GL ι R) : Matrix ι ι R) := by
            rw [ht]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [mem_stab_iff]
    intro i j
    refine ⟨low_zero_of_mul (key x _ ht) i j, ?_⟩
    rw [hinv]
    exact low_zero_of_mul (key x⁻¹ _ hx') i j
  · intro hy
    rw [mem_stab_iff] at hy
    set y : GL (ι ⊕ ι) R := B⁻¹ * x * B with hydef
    have e1 := mul_eq_of_low_zero fun i j => (hy i j).1
    have e2 := mul_eq_of_low_zero fun i j => (hy i j).2
    set m := (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁ with hm
    set m' := ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁ with hm'
    have hyy : (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hyy' : ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hmm : m * m' = 1 := by
      apply firstCols_cancel
      rw [← Matrix.mul_assoc, ← e1, Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, hyy, Matrix.one_mul, Matrix.mul_one]
    have hmm' : m' * m = 1 := by
      apply firstCols_cancel
      rw [← Matrix.mul_assoc, ← e2, Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, hyy', Matrix.one_mul, Matrix.mul_one]
    let u : GL ι R := ⟨m, m', hmm, hmm'⟩
    refine ⟨T * u * T⁻¹, ?_⟩
    have hx : (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
        (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [hydef]
      group
    calc _ = (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
          conv_lhs => rw [hD]
          simp only [Matrix.mul_assoc]
      _ = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι) * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
          rw [hx]; simp only [Matrix.mul_assoc]
      _ = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * (m * ((T⁻¹ : GL ι R) : Matrix ι ι R)) := by
          rw [e1]; simp only [Matrix.mul_assoc]
      _ = D * (T : Matrix ι ι R) * (m * ((T⁻¹ : GL ι R) : Matrix ι ι R)) := by rw [hB]
      _ = _ := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rfl

end Linear

theorem exists_isPar_iff_mem_uQ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E), b.1.toCols₁ = diagCols (Fin n) * t₀.1 → ∀ x : G2 σ Y, (∃ t, IsPar x t) ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := by
  intro F E _ _ _ _ _ σ n Y χ ε b hb t₀ ht x
  have hdiag : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E).map (inclR (F := F) (E := E) (AF F)) =
      diagCols (Fin n) := by
    ext r j
    rcases r with i | i <;> by_cases h : i = j <;> simp [diagCols, Matrix.one_apply, h]
  have hB : ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * firstCols (AE F E) (Fin n) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * ((Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)) t₀ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [mul_firstCols, ← hdiag]
    have ht' : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * (t₀.1 : Matrix (Fin n) (Fin n) E) := ht
    have := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n) E => M.map (inclR (F := F) (E := E) (AF F))) ht'
    simp only [Matrix.map_mul] at this
    exact this
  have h := exists_mul_eq_iff_mem_stab (bA (F := F) b) x.1 (diagCols (Fin n)) _ hB
  rw [PositivityTheory.RgEis.Ad.uQ, Subgroup.mem_subgroupOf, frameEquiv_val]
  exact h

end GlobalTheory.CompanionTheory.SiegelFrame.ParStab
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLattice
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {r : ℕ}


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem poisson_herm : ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∀ f : hermA D r → ℂ, Continuous f → (∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ K, ‖f (b + c.1)‖ ≤ u c) → Integrable f lam ∧ (Summable (fun t : ratHerm D r => ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) → ∑' c : ratHerm D r, f c.1 = ∑' t : ratHerm D r, ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
  intro D r ψ hψ lam 𝓖 h𝓖 f hf hu
  obtain ⟨hH, hD, hD1⟩ := h𝓖
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : LocallyCompactSpace (hermA D r) :=
    (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  haveI : Countable D.host.E := GlobalTheory.CompanionTheory.FourierComplete.countable_numberField D.host.E
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  have hmem : ∀ q : ratHerm D r, q.1.1 ∈ ratMx D r r := fun q => AddSubgroup.mem_comap.1 q.2
  haveI : Countable (ratHerm D r) := by
    choose g hg using fun q : ratHerm D r => mem_ratMx.1 (hmem q)
    exact Function.Injective.countable (f := g) fun a b h =>
      Subtype.ext (Subtype.ext (by rw [← hg a, ← hg b, h]))
  haveI := hH
  obtain ⟨-, K, hK, hKx⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := r)
  let ι : ratHerm D r →+ hermA D r := (ratHerm D r).subtype
  have hι : Function.Injective ι := Subtype.val_injective
  have hr : ι.range = ratHerm D r := AddSubgroup.range_subtype _
  have hD' : IsAddFundamentalDomain ι.range 𝓖 lam := by
    rw [hr]
    exact hD
  have hc : ∀ x : hermA D r, ∃ l ∈ ratHerm D r, x - l ∈ K := fun x => by
    obtain ⟨γ, hγ, h⟩ := hKx x
    refine ⟨-γ, neg_mem hγ, ?_⟩
    rwa [sub_neg_eq_add, add_comm]
  have hx : ∀ x : hermA D r, ∃ a, x - ι a ∈ K := fun x => by
    obtain ⟨l, hl, h⟩ := hc x
    exact ⟨⟨l, hl⟩, h⟩
  let Eh : ratHerm D r → hermA D r → ℂ := fun t b => chi ψ t.1.1 b
  have hEc : ∀ t, Continuous (Eh t) := fun t => continuous_chi hψ t.1.1
  have hEn : ∀ t b, ‖Eh t b‖ = 1 := fun t b => hψ.2.1 _
  have hEp : ∀ t x c, Eh t (x + ι c) = Eh t x := fun t x c => by
    show chi ψ t.1.1 (x + c.1) = chi ψ t.1.1 x
    rw [chi_add_right, chi_rat hψ (hmem t) c, mul_one]
  have hE0 : ∀ t, Eh t 0 = 1 := fun t => chi_zero_right ψ t.1.1
  have hself : ∀ t x, Eh t x * Eh (-t) x = 1 := fun t x => by
    show chi ψ t.1.1 x * chi ψ (-t.1.1) x = 1
    rw [← chi_add_left, add_neg_cancel, chi_zero_left]
  have horth : ∀ s t, t ≠ s → ∫ x in 𝓖, Eh t x * Eh (-s) x ∂lam = 0 := fun s t hts => by
    obtain ⟨a, ha⟩ := exists_chi_ne hψ (t - s) (sub_ne_zero.2 hts)
    have hm : t.1.1 + -s.1.1 = (t - s).1.1 := by
      rw [← sub_eq_add_neg]
      rfl
    have he : ∀ x, Eh t x * Eh (-s) x = chi ψ (t - s).1.1 x := fun x => by
      rw [← hm, chi_add_left]
      rfl
    simp only [he]
    exact Formalism.IndefR.Tow.fd_setIntegral_char_eq_zero hD (a := a)
      (fun x y => chi_add_right ψ _ x y) (fun g hg => chi_rat hψ (hmem (t - s)) ⟨g, hg⟩) ha
  have hcomp : ∀ g : hermA D r → ℂ, Continuous g → (∀ x c, g (x + ι c) = g x) →
      (∀ t, ∫ b in 𝓖, g b * Eh (-t) b ∂lam = 0) → ∀ x, g x = 0 := fun g hg hp hz x => by
    refine GlobalTheory.CompanionTheory.FourierComplete.eq_zero_of_coeffs_vanish (ratHerm D r) lam hD hK hc (T := ratHerm D r)
      Eh hEc (fun t x l hl => hEp t x ⟨l, hl⟩) (fun y => chi_zero_left ψ y) (fun s t y => chi_add_left ψ _ _ y)
      (fun t y => ?_) (fun a b hab => ?_) g hg (fun y l hl => hp y ⟨l, hl⟩) hz x
    · show star (ψ _) = chi ψ (-t.1.1) y
      rw [star_psi' hψ, chi_neg_left]
    · refine rat_of_chi hψ _ fun t => ?_
      have h1 := chi_add_right ψ t.1.1 (-a) b
      have h2 := chi_add_right ψ t.1.1 (-a) a
      rw [neg_add_cancel, chi_zero_right] at h2
      have h3 : chi ψ t.1.1 a = chi ψ t.1.1 b := hab t
      rw [h1, ← h3, ← h2]
  have hu' : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable ι f := hu
  have main := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.poisson_gen (V := hermA D r) (C := ratHerm D r) (ι := ι) hι
    (μ := lam) hD' hD1 hK hx (E := Eh) hEc hEn hEp hE0 hself horth hcomp hf hu'
  have hneg : ∀ (t : ratHerm D r) b, Eh (-t) b =
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) := fun t b => chi_neg_left ψ t.1.1 b
  simp only [hneg] at main
  exact main

end GlobalTheory.CompanionTheory.HermPoisson
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentity
section
noncomputable section

namespace GlobalTheory.CompanionTheory.MirSides

open Matrix PositivityTheory.RgEis PositivityTheory.RgEis.MG
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection
open GlobalTheory.CompanionTheory.CMMirror
open scoped NumberField.AdeleRing
open NumberField

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tInv_dgl (d : ι → IdeleGroup k) : tInv (dgl d) = dgl fun i => (d i)⁻¹ := by
  ext r c
  rw [tInv_coe]
  show (Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]))ᵀ r c =
    Matrix.diagonal (fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k])) r c
  rw [Matrix.diagonal_transpose]

theorem tInv_mem_ratGL {E R : Type} [Field E] [CommRing R] (A : Ad E R) (g : GL ι R) (h : g ∈ A.ratGL ι) :
    tInv g ∈ A.ratGL ι := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨tInv x, (tInv_map _ x).symm⟩

variable {G : Type} [Group G]

theorem kap_tInv (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (g : G) :
    kap (tInv.comp π) (fun i => (d i)⁻¹) g = tInv (kap π d g) := by
  unfold kap
  rw [MonoidHom.comp_apply, ← tInv_dgl, map_mul, map_mul, map_inv]

theorem kap_mem [TopologicalSpace G] {π : G →* GL ι 𝔸[k]} {Γ K : Subgroup G} {i₀ i₁ : ι} {ω : HeckeCharacter k}
    {d : ι → IdeleGroup k} {c : G → ℂ} {η η' l : G → ℝ} (h : MirData π Γ K i₀ i₁ ω d c η η' l) (κ : G) (hκ : κ ∈ K) :
    kap π d κ ∈ (adStd k).kGL ι := by
  obtain ⟨κ', hκ', e⟩ := h.piK κ hκ
  have e' : π κ * dgl d = dgl d * κ' := Units.ext e
  have : kap π d κ = κ' := by
    unfold kap
    rw [mul_assoc, e', inv_mul_cancel_left]
  rw [this]
  exact hκ'

theorem bdet_tInv_of_mem {R : Type} [CommRing R] {i : ι}
    (hmul : ∀ p ∈ stab R ({i} : Set ι), ∀ q ∈ stab R ({i} : Set ι),
      bdet ({i} : Set ι) (p * q) = bdet {i} p * bdet {i} q)
    (p : GL ι R) (hp : p ∈ stab R ({i}ᶜ : Set ι)) : bdet ({i} : Set ι) (tInv p) = (bdet {i} p)⁻¹ := by
  have h1 : tInv p ∈ stab R ({i} : Set ι) := (tInv_mem_stab p {i}).2 hp
  have h2 : tInv p⁻¹ ∈ stab R ({i} : Set ι) := (tInv_mem_stab p⁻¹ {i}).2 (inv_mem hp)
  have e := hmul _ h1 _ h2
  have b1 : bdet ({i} : Set ι) (1 : GL ι R) = 1 := by
    have := hmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact left_eq_mul.1 this
  rw [← map_mul, mul_inv_cancel, map_one, b1, bdet_tInv {i} p⁻¹, inv_inv] at e
  exact eq_inv_of_mul_eq_one_left e.symm

theorem lg_inv {A : Ad k 𝔸[k]} (h : A.GoodL) (b : (𝔸[k])ˣ) : A.lg b⁻¹ = - A.lg b := by
  have h1 := h.lgmul 1 1
  have h2 := h.lgmul b b⁻¹
  rw [mul_one] at h1
  rw [mul_inv_cancel] at h2
  linarith

theorem toIdele_inv {ω : HeckeCharacter k} (h : ω * ω = 1) (b : IdeleGroup k) :
    ω.toIdele b⁻¹ = ω.toIdele b := by
  have e : ω.toIdele b * ω.toIdele b = 1 := by
    rw [HeckeCharacter.toIdele_apply]
    exact DFunLike.congr_fun h (IdeleClassGroup.mk k b)
  rw [map_inv]
  exact inv_eq_of_mul_eq_one_right e

theorem modPow_one_eq (x : IdeleGroup k) :
    modPow x 1 = Complex.exp ((adStd k).lg x : ℝ) := by
  have hp : 0 < (IdeleGroup.ideleModule k x : ℝ) := (IdeleGroup.ideleModule k x).2
  show _ = Complex.exp ((Real.log (IdeleGroup.ideleModule k x : ℝ) : ℝ) : ℂ)
  rw [← Complex.ofReal_exp, Real.exp_log hp, modPow, Complex.cpow_one]

theorem sideOf : StdGood → BdetLaw → SideOf := by
  intro hS hB G _ _ _ _ K _ k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l h
  have hG := hS k
  have hmul := (hB k 𝔸[k] (adStd k) hG ι {i₁}).2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      { two := h.two
        sq := h.sq
        cont := h.cont
        piK := kap_mem h
        piΓ := h.piΓ
        trans := h.trans _ (Or.inl rfl)
        mem := fun _ => Iff.rfl
        par := h.par
        ht := h.ht
        val := fun p hp => h.val p hp }
  · refine
      { two := h.two
        sq := h.sq
        cont := cont_tInv.comp h.cont
        piK := fun κ hκ => ?_
        piΓ := fun γ hγ => tInv_mem_ratGL _ _ (h.piΓ γ hγ)
        trans := fun g hg => ?_
        mem := fun g => (tInv_mem_stab (π g) {i₁}).symm
        par := h.par'
        ht := h.ht'
        val := fun p hp => ?_ }
    · rw [kap_tInv]
      exact tInv_mem_kGL _ _ (kap_mem h κ hκ)
    · obtain ⟨γ, hγ, e⟩ := h.trans {i₁}ᶜ (Or.inr rfl) (tInv g) (tInv_mem_ratGL _ _ hg)
      refine ⟨γ, hγ, ?_⟩
      have e' := (tInv_mem_stab _ {i₁}).2 e
      rw [map_mul, tInv_tInv, map_inv] at e'
      exact e'
    · have hp' : π p ∈ stab 𝔸[k] ({i₁}ᶜ : Set ι) := hp
      have hb := bdet_tInv_of_mem hmul (π p) hp'
      obtain ⟨v1, v2⟩ := h.val' p hp'
      refine ⟨?_, ?_⟩
      · show c p = ω.toIdele (bdet {i₁} (tInv (π p)))
        rw [hb, toIdele_inv h.sq]
        exact v1
      · show η' p = (adStd k).lg (bdet {i₁} (tInv (π p)))
        rw [hb, lg_inv hG]
        exact v2
  · intro g
    rw [map_mul, tInv_dgl]
    rfl
  · intro g
    rw [map_mul, modPow_mul, modPow_one_eq (Matrix.GeneralLinearGroup.det (π g)), ← h.vall g]

end GlobalTheory.CompanionTheory.MirSides
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetClosedOpenSequenceStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.twisted_jacquet_closed_open_sequence : ∀ {G M Z VC VO AC AO : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    [AddCommGroup Z] [Module ℂ Z] [AddCommGroup VC] [Module ℂ VC] [AddCommGroup VO] [Module ℂ VO]
    [AddCommGroup AC] [Module ℂ AC] [AddCommGroup AO] [Module ℂ AO]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (hUn : U.Normal) (θ : U →* ℂˣ)
    (hθ : IsOpen (θ.ker : Set U))
    (hdir : ∀ L₁ L₂ : Subgroup G, L₁ ≤ U → L₂ ≤ U → IsCompact (L₁ : Set G) → IsCompact (L₂ : Set G) →
      ∃ L : Subgroup G, L ≤ U ∧ IsCompact (L : Set G) ∧ L₁ ≤ L ∧ L₂ ≤ L)
    (s : M →* G) (c : M →* ℂˣ) (ρ : Representation ℂ M (TwJacquet (cInd H σ) U θ))
    (hρ : ∀ (m : M) (f : cIndSpace H σ), ρ m (Submodule.Quotient.mk f) =
      ((c m : ℂˣ) : ℂ) • Submodule.Quotient.mk (cInd H σ (s m) f))
    (C : Set G) (hCc : IsClosed C) (hHC : ∀ h ∈ H, ∀ x ∈ C, h * x ∈ C) (hCU : ∀ x ∈ C, ∀ u ∈ U, x * u ∈ C)
    (πC : Representation ℂ M VC) (πO : Representation ℂ M VO)
    (aC : Representation ℂ M AC) (aO : Representation ℂ M AO)
    (jC : VC →ₗ[ℂ] AC) (jO : VO →ₗ[ℂ] AO) (hjC : Function.Injective jC) (hjO : Function.Injective jO)
    (hjCe : ∀ m v, jC (πC m v) = aC m (jC v)) (hjOe : ∀ m v, jO (πO m v) = aO m (jO v))
    (eC : cIndSpace H σ →ₗ[ℂ] AC) (eO : cIndSpace H σ →ₗ[ℂ] AO)
    (hC1 : ∀ (u : U) f, eC (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eC f)
    (hO1 : ∀ (u : U) f, eO (cInd H σ (u : G) f) = ((θ u : ℂˣ) : ℂ) • eO f)
    (hCs : ∀ m f, aC m (eC f) = ((c m : ℂˣ) : ℂ) • eC (cInd H σ (s m) f))
    (hOs : ∀ m f, aO m (eO f) = ((c m : ℂˣ) : ℂ) • eO (cInd H σ (s m) f))
    (hCmem : ∀ f, ∃ v, jC v = eC f)
    (hOmem : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → ∃ v, jO v = eO f)
    (hConto : ∀ v, ∃ f, eC f = jC v)
    (hOonto : ∀ v, ∃ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) ∧ eO f = jO v)
    (hCoff : ∀ f : cIndSpace H σ, (∀ x ∈ C, (f : smoothPart (ind H σ)).1.1 x = 0) → eC f = 0)
    (hlocC : ∀ f, eC f = 0 → ∀ p ∈ C, AvgVanish H σ U θ f p)
    (hlocO : ∀ f, eO f = 0 → ∀ p, p ∉ C → AvgVanish H σ U θ f p),
  ∃ S : Subrepresentation ρ, Nonempty ((subQuot S ⊥).Equiv πO) ∧ Nonempty ((subQuot ⊤ S).Equiv πC) := by
  intro G M Z VC VO AC AO _ _ _ _ _ _ _ _ _ _ _ _ _ _
    H σ U hUn θ hθ hdir s c ρ hρ C hCc hHC hCU πC πO aC aO jC jO hjC hjO hjCe hjOe
    eC eO hC1 hO1 hCs hOs hCmem hOmem hConto hOonto hCoff hlocC hlocO
  have kC : twKer (cInd H σ) U θ ≤ LinearMap.ker eC := Submodule.span_le.2 (by
    rintro _ ⟨u, v, rfl⟩
    show eC _ = 0
    rw [map_sub, hC1, map_smul, sub_self])
  have kO : twKer (cInd H σ) U θ ≤ LinearMap.ker eO := Submodule.span_le.2 (by
    rintro _ ⟨u, v, rfl⟩
    show eO _ = 0
    rw [map_sub, hO1, map_smul, sub_self])
  have ECmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eC kC (Submodule.Quotient.mk f) = eC f := fun f => rfl
  have EOmk : ∀ f, (twKer (cInd H σ) U θ).liftQ eO kO (Submodule.Quotient.mk f) = eO f := fun f => rfl
  refine Glue.extension_of_maps ρ πC πO aC aO jC jO hjC hjO hjCe hjOe
    ((twKer (cInd H σ) U θ).liftQ eC kC) ((twKer (cInd H σ) U θ).liftQ eO kO) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro m y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hρ, map_smul, ECmk, ECmk, hCs]
  · intro m y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hρ, map_smul, EOmk, EOmk, hOs]
  · intro y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact hCmem f
  · intro v
    obtain ⟨f, hf⟩ := hConto v
    exact ⟨Submodule.Quotient.mk f, hf⟩
  · intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hv⟩ := Glue.glue H σ U hUn θ hθ hdir C hCc hHC hCU f (hlocC f hy)
    have e : (Submodule.Quotient.mk f : TwJacquet (cInd H σ) U θ) = Submodule.Quotient.mk g :=
      (Submodule.Quotient.eq _).2 hg
    obtain ⟨v, hv'⟩ := hOmem g hv
    exact ⟨v, by rw [e, EOmk, hv']⟩
  · intro y hyC hyO
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hv⟩ := Glue.glue H σ U hUn θ hθ hdir Set.univ isClosed_univ (fun _ _ _ _ => trivial)
      (fun _ _ _ _ => trivial) f (fun p _ => by
        by_cases hp : p ∈ C
        · exact hlocC f hyC p hp
        · exact hlocO f hyO p hp)
    have hg0 : g = 0 := Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => hv x trivial)))
    rw [hg0, sub_zero] at hg
    exact (Submodule.Quotient.mk_eq_zero _).2 hg
  · intro v
    obtain ⟨f, hf, he⟩ := hOonto v
    exact ⟨Submodule.Quotient.mk f, hCoff f hf, he⟩
end

