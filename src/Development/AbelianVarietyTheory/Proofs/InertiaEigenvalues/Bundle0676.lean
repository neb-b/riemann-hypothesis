module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFourierExpansionConjugateHalfSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.FinFourier

variable {D : D7}

theorem interp_of_sep {α : Type} [DecidableEq α] (P : Set (α → ℂ)) (h1 : (1 : α → ℂ) ∈ P)
    (hmul : ∀ f ∈ P, ∀ g ∈ P, f * g ∈ P) (hadd : ∀ f ∈ P, ∀ g ∈ P, f + g ∈ P)
    (hsmul : ∀ (c : ℂ), ∀ f ∈ P, c • f ∈ P) (K : Set α) (s : Finset α) (rep : α → α)
    (hrep : ∀ x ∈ K, rep x ∈ s)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ g ∈ P, g a ≠ g b ∧ ∀ x ∈ K, g x = g (rep x))
    (f : α → ℂ) (hf : ∀ x ∈ K, f x = f (rep x)) : ∃ F ∈ P, ∀ x ∈ K, f x = F x := by
  have h0 : (0 : α → ℂ) ∈ P := by simpa using hsmul 0 1 h1
  have hsum : ∀ (t : Finset α) (u : α → α → ℂ), (∀ a ∈ t, u a ∈ P) → (∑ a ∈ t, u a) ∈ P := by
    intro t u hu
    induction t using Finset.induction_on with
    | empty => simpa using h0
    | insert b t hb ih =>
      rw [Finset.sum_insert hb]
      exact hadd _ (hu _ (Finset.mem_insert_self _ _)) _ (ih fun a ha => hu a (Finset.mem_insert_of_mem ha))
  have hprod : ∀ (t : Finset α) (u : α → α → ℂ), (∀ a ∈ t, u a ∈ P) → (∏ a ∈ t, u a) ∈ P := by
    intro t u hu
    induction t using Finset.induction_on with
    | empty => simpa using h1
    | insert b t hb ih =>
      rw [Finset.prod_insert hb]
      exact hmul _ (hu _ (Finset.mem_insert_self _ _)) _ (ih fun a ha => hu a (Finset.mem_insert_of_mem ha))
  have hsep' : ∀ a b : α, ∃ g : α → ℂ, a ∈ s → b ∈ s → a ≠ b → g ∈ P ∧ g a ≠ g b ∧ ∀ x ∈ K, g x = g (rep x) := by
    intro a b
    by_cases h : a ∈ s ∧ b ∈ s ∧ a ≠ b
    · obtain ⟨g, hg⟩ := hsep a h.1 b h.2.1 h.2.2
      exact ⟨g, fun _ _ _ => hg⟩
    · exact ⟨0, fun ha hb hab => absurd ⟨ha, hb, hab⟩ h⟩
  choose g hg using hsep'
  let δ : α → α → ℂ := fun a => ∏ b ∈ s.erase a, (g a b a - g a b b)⁻¹ • (g a b + (-(g a b b)) • (1 : α → ℂ))
  have hδP : ∀ a ∈ s, δ a ∈ P := fun a ha => hprod _ _ fun b hb => hsmul _ _ (hadd _
    (hg a b ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm).1 _ (hsmul _ _ h1))
  have hδ : ∀ a ∈ s, ∀ x ∈ K, δ a x = if rep x = a then 1 else 0 := by
    intro a ha x hx
    simp only [δ, Finset.prod_apply, Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
    split_ifs with hxa
    · apply Finset.prod_eq_one
      intro b hb
      have hb' := hg a b ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm
      rw [hb'.2.2 x hx, hxa]
      have : g a b a - g a b b ≠ 0 := sub_ne_zero.2 hb'.2.1
      rw [mul_one, ← sub_eq_add_neg, inv_mul_cancel₀ this]
    · apply Finset.prod_eq_zero (i := rep x)
      · exact Finset.mem_erase.2 ⟨hxa, hrep x hx⟩
      · have hb' := hg a (rep x) ha (hrep x hx) (Ne.symm hxa)
        rw [hb'.2.2 x hx]
        ring
  refine ⟨∑ a ∈ s, f a • δ a, hsum _ _ fun a ha => hsmul _ _ (hδP a ha), fun x hx => ?_⟩
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun a ha => by rw [hδ a ha x hx]]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq s (rep x) f, if_pos (hrep x hx), hf x hx]

theorem finite_cover_pow {O K : Type} [CommRing O] [Field K] [Algebra O K] (ϖ : O) (hϖ : algebraMap O K ϖ ≠ 0)
    (N M : ℕ) (hfin : Finite (O ⧸ Ideal.span {ϖ ^ (N + M)})) (m n : Type) [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] :
    ∃ T : Finset (Matrix m n K), ∀ X : Matrix m n K,
      (∀ i j, ∃ o : O, algebraMap O K (ϖ ^ N) * X i j = algebraMap O K o) →
      ∃ t ∈ T, ∀ i j, ∃ o : O, (X - t) i j = algebraMap O K (ϖ ^ M * o) := by
  classical
  set I : Ideal O := Ideal.span {ϖ ^ (N + M)} with hIdef
  have ha : algebraMap O K (ϖ ^ N) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hϖ
  haveI : Finite (m → n → O ⧸ I) := inferInstance
  haveI : Fintype (m → n → O ⧸ I) := Fintype.ofFinite _
  let lift : (m → n → O ⧸ I) → m → n → O :=
    fun q i j => Function.surjInv (Ideal.Quotient.mk_surjective (I := I)) (q i j)
  refine ⟨Finset.univ.image fun q => Matrix.of fun i j => (algebraMap O K (ϖ ^ N))⁻¹ * algebraMap O K (lift q i j), ?_⟩
  intro X hX
  choose z hz using hX
  let q : m → n → O ⧸ I := fun i j => Ideal.Quotient.mk I (z i j)
  refine ⟨_, Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, fun i j => ?_⟩
  have hq : Ideal.Quotient.mk I (lift q i j) = Ideal.Quotient.mk I (z i j) :=
    Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := I)) _
  rw [Ideal.Quotient.eq, hIdef, Ideal.mem_span_singleton'] at hq
  obtain ⟨w, hw⟩ := hq
  refine ⟨-w, ?_⟩
  have hij := hz i j
  simp only [Matrix.sub_apply, Matrix.of_apply]
  have hX : X i j = (algebraMap O K (ϖ ^ N))⁻¹ * algebraMap O K (z i j) := by
    rw [← hij, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have hzl : z i j - lift q i j = ϖ ^ N * (ϖ ^ M * -w) := by
    rw [← neg_sub, ← hw]; ring
  rw [hX, ← mul_sub, ← map_sub, hzl, map_mul (algebraMap O K) (ϖ ^ N), ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

end GlobalTheory.DownLift.GenSplit.FinFourier

namespace GlobalTheory.DownLift.GenSplit


open GlobalTheory.SplitScalar in
theorem finite_fourier_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (ϖ : OI v), Irreducible ϖ → ∀ (M N : ℕ), (∀ x : WO S T, IsHalf (cA D e) x → ¬ InPow ϖ M (adjCo φ S T BS BT x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T BS BT e ϖ M, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1) → ∀ (a : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ), (∀ X Z, InPow ϖ M Z → a (X + Z) = a X) → ∃ c : WO S T →₀ ℂ, (∀ y ∈ c.support, IsHalf e y) ∧ ∀ x, IsHalf (cA D e) x → Bdd ϖ N (adjCo φ S T BS BT x) → a (adjCo φ S T BS BT x) = c.sum fun y z => z * ψ (symplO S T x y) := by
  intro D ψ _ S T ΛS ΛT _ _ v φ e _ BS BT ϖ hϖ M N hyp a ha
  classical

  let P : Set (WO S T → ℂ) := {F | ∃ c : WO S T →₀ ℂ, (∀ y ∈ c.support, IsHalf e y) ∧
    ∀ x, F x = c.sum fun y z => z * ψ (symplO S T x y)}
  have h0 : ∀ x : WO S T, ∀ y : WO S T, (0 : ℂ) * ψ (symplO S T x y) = 0 := fun _ _ => zero_mul _
  have hP1 : (1 : WO S T → ℂ) ∈ P := ⟨Finsupp.single 0 1, fun y hy => by
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy)]; exact isHalf_zero e, fun x => by
    rw [Finsupp.sum_single_index (h0 x 0), symplO_zero_right, AddChar.map_zero_eq_one, one_mul]; rfl⟩
  have hPadd : ∀ f ∈ P, ∀ g ∈ P, f + g ∈ P := by
    rintro f ⟨c, hc, hf⟩ g ⟨d, hd, hg⟩
    refine ⟨c + d, fun y hy => ?_, fun x => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hy) with h | h
      · exact hc y h
      · exact hd y h
    · rw [Pi.add_apply, hf, hg, Finsupp.sum_add_index' (fun y => h0 x y) (fun _ _ _ => add_mul _ _ _)]
  have hPsmul : ∀ (r : ℂ), ∀ f ∈ P, r • f ∈ P := by
    rintro r f ⟨c, hc, hf⟩
    refine ⟨r • c, fun y hy => hc y (Finsupp.support_smul hy), fun x => ?_⟩
    rw [Pi.smul_apply, hf, Finsupp.sum_smul_index' (fun y => h0 x y), smul_eq_mul, Finsupp.mul_sum]
    simp only [smul_eq_mul, mul_assoc]
  have hPmul : ∀ f ∈ P, ∀ g ∈ P, f * g ∈ P := by
    rintro f ⟨c, hc, hf⟩ g ⟨d, hd, hg⟩
    refine ⟨c.sum fun y z => d.sum fun y' z' => Finsupp.single (y + y') (z * z'), fun y hy => ?_, fun x => ?_⟩
    · obtain ⟨y₁, hy₁, hy⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy)
      obtain ⟨y₂, hy₂, hy⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy)
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy)]
      exact isHalf_add (hc y₁ hy₁) (hd y₂ hy₂)
    · rw [Pi.mul_apply, hf, hg, Finsupp.sum_sum_index (fun y => h0 x y) (fun _ _ _ => add_mul _ _ _),
        Finsupp.sum_mul]
      refine Finsupp.sum_congr fun y _ => ?_
      rw [Finsupp.sum_sum_index (fun y => h0 x y) (fun _ _ _ => add_mul _ _ _), Finsupp.mul_sum]
      refine Finsupp.sum_congr fun y' _ => ?_
      rw [Finsupp.sum_single_index (h0 x _), GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul]
      ring

  let H : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)) :=
    { carrier := {X | InPow ϖ M X}
      add_mem' := fun {X Y} hX hY i j => by
        obtain ⟨o₁, h₁⟩ := hX i j
        obtain ⟨o₂, h₂⟩ := hY i j
        exact ⟨o₁ + o₂, by rw [Matrix.add_apply, h₁, h₂, ← map_add (f := _), mul_add]⟩
      zero_mem' := fun i j => ⟨0, by simp⟩
      neg_mem' := fun {X} hX i j => by
        obtain ⟨o, h⟩ := hX i j
        exact ⟨-o, by rw [Matrix.neg_apply, h, ← map_neg, mul_neg]⟩ }
  have hadj : ∀ x y : WO S T, adjCo φ S T BS BT (x - y) = adjCo φ S T BS BT x - adjCo φ S T BS BT y := by
    intro x y
    have e1 : (x - y : WO S T).map (cA D) = x.map (cA D) - y.map (cA D) := by ext i j; simp
    have e2 : ∀ {m n : Type} (A B : Matrix m n (AE D)),
        (A - B).map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) = A.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) - B.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) :=
      fun A B => by ext i j; simp
    simp only [adjCo, e1, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, e2]
  let q : WO S T → Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) ⧸ H :=
    fun x => (adjCo φ S T BS BT x : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) ⧸ H)
  have hqeq : ∀ x y, q x = q y ↔ InPow ϖ M (adjCo φ S T BS BT (x - y)) := by
    intro x y
    rw [hadj]
    exact QuotientAddGroup.eq_iff_sub_mem
  let K : Set (WO S T) := {x | IsHalf (cA D e) x ∧ Bdd ϖ N (adjCo φ S T BS BT x)}
  have hϖ0 : algebraMap (OI v) (Fv D.host.F v) ϖ ≠ 0 :=
    (FaithfulSMul.algebraMap_injective (OI v) (Fv D.host.F v)).ne_iff' (map_zero _) |>.2 hϖ.ne_zero
  have hfin : Finite (OI v ⧸ Ideal.span {ϖ ^ (N + M)}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero _ hϖ.ne_zero)
  obtain ⟨T₀, hT₀⟩ := FinFourier.finite_cover_pow ϖ hϖ0 N M hfin (Fin S.rank) (Fin T.rank)
  have hfinK : (q '' K).Finite := by
    refine (T₀.finite_toSet.image (QuotientAddGroup.mk (s := H))).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, h⟩ := hT₀ _ hx.2
    exact ⟨t, ht, (QuotientAddGroup.eq_iff_sub_mem (N := H)).2 (show InPow ϖ M _ from h) |>.symm⟩
  let pick : (Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) ⧸ H) → WO S T :=
    fun c => if h : ∃ x ∈ K, q x = c then h.choose else 0
  have hpick : ∀ x ∈ K, pick (q x) ∈ K ∧ q (pick (q x)) = q x := by
    intro x hx
    have h : ∃ x' ∈ K, q x' = q x := ⟨x, hx, rfl⟩
    simp only [pick, dif_pos h]
    exact h.choose_spec
  have hsep : ∀ a' ∈ hfinK.toFinset.image pick, ∀ b' ∈ hfinK.toFinset.image pick, a' ≠ b' →
      ∃ g ∈ P, g a' ≠ g b' ∧ ∀ x ∈ K, g x = g (pick (q x)) := by
    intro a' ha' b' hb' hab
    obtain ⟨c₁, hc₁, rfl⟩ := Finset.mem_image.1 ha'
    obtain ⟨x₁, hx₁, rfl⟩ := hfinK.mem_toFinset.1 hc₁
    obtain ⟨c₂, hc₂, rfl⟩ := Finset.mem_image.1 hb'
    obtain ⟨x₂, hx₂, rfl⟩ := hfinK.mem_toFinset.1 hc₂
    have A := hpick x₁ hx₁
    have B := hpick x₂ hx₂
    have hne : ¬ InPow ϖ M (adjCo φ S T BS BT (pick (q x₁) - pick (q x₂))) := by
      intro h
      apply hab
      have h' := (hqeq _ _).2 h
      rw [A.2, B.2] at h'
      rw [h']
    obtain ⟨y, hy, hyL, hyne⟩ := hyp _ (isHalf_sub A.1.1 B.1.1) hne
    refine ⟨fun x => ψ (symplO S T x y), ⟨Finsupp.single y 1, fun y' hy' => ?_, fun x => ?_⟩, ?_, ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy')]; exact hy
    · rw [Finsupp.sum_single_index (h0 x y), one_mul]
    · intro h
      apply hyne
      simp only at h
      rw [symplO_sub_left, sub_eq_add_neg, AddChar.map_add_eq_mul, h, ← AddChar.map_add_eq_mul, add_neg_cancel,
        AddChar.map_zero_eq_one]
    · intro x hx
      have hxr : x - pick (q x) ∈ halfPow φ S T BS BT e ϖ M :=
        ⟨isHalf_sub hx.1 (hpick x hx).1.1, (hqeq _ _).1 (hpick x hx).2.symm⟩
      show ψ (symplO S T x y) = ψ (symplO S T (pick (q x)) y)
      conv_lhs => rw [← add_sub_cancel (pick (q x)) x]
      rw [GlobalTheory.LatVac.symplO_add_left, AddChar.map_add_eq_mul, hyL _ hxr, mul_one]
  have hf : ∀ x ∈ K, a (adjCo φ S T BS BT x) = a (adjCo φ S T BS BT (pick (q x))) := by
    intro x hx
    have hI := (hqeq _ _).1 (hpick x hx).2.symm
    rw [hadj] at hI
    have h := ha (adjCo φ S T BS BT (pick (q x))) _ hI
    rwa [add_sub_cancel] at h
  obtain ⟨F, ⟨c, hc, hF⟩, hFK⟩ := FinFourier.interp_of_sep P hP1 hPmul hPadd hPsmul K
    (hfinK.toFinset.image pick) (fun x => pick (q x))
    (fun x hx => Finset.mem_image.2 ⟨q x, hfinK.mem_toFinset.2 ⟨x, hx, rfl⟩, rfl⟩) hsep
    (fun x => a (adjCo φ S T BS BT x)) hf
  exact ⟨c, hc, fun x hx hB => (hFK x ⟨hx, hB⟩).trans (hF x)⟩

end GlobalTheory.DownLift.GenSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CongIndex

theorem bounded_cover {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {J : Subgroup (GAf L n)}
    (hJ : IsBounded J) {M : ℕ} (hM : 0 < M) :
    ∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, NG.Cong L n M (f⁻¹ * κ) := by
  classical
  obtain ⟨F0, hF0⟩ := hJ
  obtain ⟨F1, hF1⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hM
  refine ⟨(F0 ×ˢ F1).image (fun p => p.1 * p.2), fun κ hκ => ?_⟩
  obtain ⟨f0, hf0, hu⟩ := hF0 κ hκ
  obtain ⟨j, hj, κ', hκ', e⟩ := hF1 _ hu
  refine ⟨f0 * j, Finset.mem_image.2 ⟨(f0, j), Finset.mem_product.2 ⟨hf0, hj⟩, rfl⟩, ?_⟩
  have h1 : (f0 * j)⁻¹ * κ = κ' := by
    rw [mul_inv_rev, mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h1]
  exact hκ'

theorem finite_index_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)),
    IsBounded J → ∀ (h : GAf L n) (N : ℕ), 0 < N →
      (∃ N' : ℕ, 0 < N' ∧ ∀ κ, NG.Cong L n N' κ → NG.Cong L n N (h⁻¹ * κ * h)) ∧
      (∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, NG.Cong L n N (f⁻¹ * κ)) ∧
      IsBounded (J.map (MulAut.conj h).toMonoidHom) := by
  intro L _ _ _ n J hJ h N hN
  refine ⟨GlobalTheory.CongConjugate.congConj L n h N hN, bounded_cover hJ hN, ?_⟩
  classical
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h⁻¹ 1 one_pos
  obtain ⟨F, hF⟩ := bounded_cover hJ hN'
  refine ⟨F.image (fun f => h * f * h⁻¹), fun x hx => ?_⟩
  obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨f, hf, hcf⟩ := hF κ hκ
  refine ⟨h * f * h⁻¹, Finset.mem_image_of_mem _ hf, ?_⟩
  have hu := (hc _ hcf).1
  have e : (h * f * h⁻¹)⁻¹ * (MulAut.conj h).toMonoidHom κ = h⁻¹⁻¹ * (f⁻¹ * κ) * h⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
  rw [e]
  exact hu

end GlobalTheory.CongIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteModuleKilledByPowOfNotIsUnit
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory

theorem finite_module_killed_by_pow_of_not_isUnit :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (lam : O), ¬ IsUnit lam →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], ∃ a : ℕ, ∀ x : X, lam ^ a • x = 0 := by
  intro O _ _ lam hlam X _ _ _
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes (R := O) X lam
  set Y : Submodule O X := LinearMap.range (lam ^ n • (LinearMap.id : X →ₗ[O] X)) with hY
  have hFG : Y.FG := Module.Finite.iff_fg.mp inferInstance
  have hle : Y ≤ Ideal.span {lam} • Y := by
    intro y hy
    have hy' : y ∈ LinearMap.range (lam ^ (n + 1) • (LinearMap.id : X →ₗ[O] X)) := by
      rw [← hn (n + 1) (Nat.le_succ n)]; exact hy
    obtain ⟨x, rfl⟩ := hy'
    have hmem : lam ^ n • x ∈ Y := ⟨x, by simp⟩
    have : (lam ^ (n + 1) • (LinearMap.id : X →ₗ[O] X)) x = lam • (lam ^ n • x) := by
      simp [pow_succ', mul_smul]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self lam) hmem
  have hjac : Ideal.span {lam} ≤ (⊥ : Ideal O).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal lam).mpr hlam
  have hbot : Y = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ Y hFG hle hjac
  refine ⟨n, fun x => ?_⟩
  have : lam ^ n • x ∈ Y := ⟨x, by simp⟩
  rw [hbot] at this
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H0VanishOfZeroMultiplicity
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InvJump

open Module

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

def qRep (ρ : Representation LL G V) (p : Submodule LL V) (hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p) :
    Representation LL G (V ⧸ p) where
  toFun g := p.mapQ p (ρ g) (fun x hx => hp g x hx)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

end Gen

theorem h0V_eq_bot_of_multV_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), IsDR (P.PD K) ρ → multV (P.PD K) ρ τ 0 = 0 → H0V ρ = ⊥ := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ τ hdR hm
  haveI := K.2
  haveI := LL.2
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := Submodule.ne_bot_iff _ |>.1 hne
  have hinv : ∀ g, ρ g v = v := by
    intro g
    have := (Submodule.mem_iInf _).1 hv g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this

  let σ : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1) := 1
  let ι : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] V := (LinearMap.proj 0).smulRight v
  have hι : ∀ u, ι u = u 0 • v := fun u => rfl
  have hιeq : ∀ g x, ι (σ g x) = ρ g (ι x) := by
    intro g x
    rw [hι, hι, map_smul, hinv]
    rfl
  have hιinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker, hι] at hu
    have h0 : u 0 = 0 := (smul_eq_zero.1 hu).resolve_right hv0
    funext c
    rw [Subsingleton.elim c 0, h0]
    rfl
  let p : Submodule ↥LL.1 V := LinearMap.range ι
  have hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p := by
    rintro g _ ⟨u, rfl⟩
    exact ⟨σ g u, hιeq g u⟩
  let ρ₂ := GlobalTheory.InvJump.qRep ρ p hp
  have hπeq : ∀ g x, p.mkQ (ρ g x) = ρ₂ g (p.mkQ x) := fun g x => rfl
  obtain ⟨-, -, hadd⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI T K LL (Fin 1 → ↥LL.1) σ V ρ (V ⧸ p) ρ₂
    ι p.mkQ hιeq hπeq hιinj (Submodule.mkQ_surjective p) (Submodule.ker_mkQ p).symm hdR
  have h1 : multV (P.PD K) σ τ 0 = 1 := by
    have := GlobalTheory.PtCore.multV_cycPow_line (P.PD K) (GlobalTheory.DRFil.isField_dR T)
      (GlobalTheory.TopSteps.CrysRules.exists_inverse_fontaineElement_mem_fil_neg_one T K) σ 0 (fun g u => by simp [σ]) τ 0
    simpa using this
  have h2 := (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL (V ⧸ p) ρ₂ τ 0).2.1
  have h3 := (hadd τ 0).2.1
  omega

end GlobalTheory.InvJump
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeriesStatement
section
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (α : Fin n → ℂˣ),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    HasSatake π α → GlobalTheory.LFun.HasSatGL w π (Finset.univ.val.map α) := by
  first | exact @GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake | exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake | (intros; apply GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostCompletionLeMaxUnramifiedPadic
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubLoc

theorem sqrtKur_holds (l : ℕ) [Fact l.Prime] : SqrtKur l := fun p hp h4 hne y hy =>
  GlobalTheory.SqrtUnram.sqrt_neg_prime_mem_Kur l p hp h4 (Ne.symm hne) y hy

theorem kw_le_Kur_all : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i) := by
  intro D i hl2 hq hd w hw
  exact kw_le_Kur_of_ne i (UpperTheory.Small.not_dvd_condN D.host (D.nd.lPrime i).out hl2 hq hd) w hw

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldUnramified
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.HubLoc

theorem localField_unramified : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 ∧ (D.nbr i w hw).Kw.1 ≤ Loc.Ks (D.nbr i w hw).Kw 1 ∧ Loc.Good (D.nbr i w hw).Kw 1 (D.nbr i w hw).LL := by
  intro D i hs hq hd w hw
  have h2 : D.nd.l i ≠ 2 := fun e => hs (e ▸ D.host.toHostRaw.two_mem_small)
  have hN : ¬ D.nd.l i ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small (Fact.out : (D.nd.l i).Prime)).1 h with h | h | h
    exacts [hs h, hq h, hd h]
  have hK := kw_le_Kur_of_ne i hN w hw
  have h1 := le_Ks_one_of_Kur _ hK
  exact ⟨inf_eq_left.2 hK, h1, (D.self_good i w hw).good_one (D.nbr i w hw).LL_split h2 h1⟩

end GlobalTheory.HubLoc
end

