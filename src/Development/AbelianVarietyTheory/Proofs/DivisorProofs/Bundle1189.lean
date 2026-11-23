module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlag
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
open Formalism.UG (cT)

noncomputable section

namespace GlobalTheory.LeviFlag

private theorem cT_mul_lemma {A : Type} [CommRing A] (s : A →+* A) {a b c : ℕ} (P : Matrix (Fin a) (Fin b) A)
    (Q : Matrix (Fin b) (Fin c) A) : Formalism.UG.cT s (P * Q) = Formalism.UG.cT s Q * Formalism.UG.cT s P := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_cT_of_involutive {A : Type} [CommRing A] (s : A →+* A) (hs : ∀ x, s (s x) = x) {a b : ℕ}
    (P : Matrix (Fin a) (Fin b) A) : Formalism.UG.cT s (Formalism.UG.cT s P) = P := by
  unfold Formalism.UG.cT
  ext i j
  simp [hs]

private theorem cT_one_divisor {A : Type} [CommRing A] (s : A →+* A) {a : ℕ} :
    Formalism.UG.cT s (1 : Matrix (Fin a) (Fin a) A) = 1 := by
  unfold Formalism.UG.cT
  rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

private theorem cT_Y_J_X_eq_one_and_complement_eq_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n r : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (hσ : ∀ x, σ (σ x) = x) {X Y : Matrix (Fin n) (Fin r) E}
    (hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0) (hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1) :
    Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 ∧
      Formalism.UG.cT (σ : E →+* E) Y * J * J⁻¹ * Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Y * J) = 0 := by
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => hσ x
  have hJJ : Formalism.UG.cT (σ : E →+* E) J = J := by
    unfold Formalism.UG.cT
    ext i j
    simp [hJ.1 i j]
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  constructor
  · have e := congrArg (Formalism.UG.cT (σ : E →+* E)) hxy
    rw [cT_mul_lemma, cT_mul_lemma, cT_cT_of_involutive _ hs, hJJ, cT_one_divisor, ← Matrix.mul_assoc] at e
    exact e
  · rw [cT_mul_lemma, cT_cT_of_involutive _ hs, hJJ, Matrix.mul_nonsing_inv_cancel_right _ _ hdet, ← Matrix.mul_assoc]
    exact hyy

private theorem exists_unipFlag_mul_leviFlag_eq_of_mem_parFlag (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ)
    (hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0) (hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0)
    (hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1) (p : GAd σ J) (hp : p ∈ parFlag σ J X d) :
    ∃ u ∈ unipFlag σ J X d, ∃ m ∈ leviFlag σ J X Y d, p = u * m ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) := by
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma h
  obtain ⟨hL, hLL⟩ := cT_Y_J_X_eq_one_and_complement_eq_zero σ hJ hσ hyy hxy
  have hdM : ∀ j, d j < ∑ i, d i + 1 := fun j =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  have hm : ∀ a b, adjA σ J (a * b) = adjA σ J b * adjA σ J a := adjA_mul hJ
  have hi : ∀ a, adjA σ J (adjA σ J a) = a := adjA_adjA hJ hσ
  have hε : CompleteOrthogonalIdempotents (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))) :=
    idemA_complete hJ X _ hL hxx hLL
  have h1 : adjA σ J 1 = 1 := by
    have e := hm (adjA σ J 1) 1
    simp only [mul_one, hi] at e
    exact e.symm
  have hτ : ∀ a, adjA σ J (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a) =
      fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) (Option.map Sum.swap a) := by
    rintro (_ | j | j)
    · show adjA σ J (1 - ∑ j, Sum.elim (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))
          (fun j => adjA σ J (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j)) j) =
        1 - ∑ j, Sum.elim (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))
          (fun j => adjA σ J (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j)) j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, h1, map_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, hi]
      rw [add_comm]
    · rfl
    · exact hi _
  have hw : ∀ a, wt d (∑ i, d i + 1) (Option.map Sum.swap a) = - wt d (∑ i, d i + 1) a := by
    rintro (_ | j | j) <;> simp [wt]
  have hττ : ∀ a : Option (Fin r ⊕ Fin r), Option.map Sum.swap (Option.map Sum.swap a) = a := by
    rintro (_ | j | j) <;> rfl
  have hxy1 : (matHom _ σ J p).1 * (matHom _ σ J p⁻¹).1 = 1 := by
    rw [map_inv]
    exact Units.mul_inv _
  have hyx1 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [map_inv]
    exact Units.inv_mul _
  obtain ⟨m, m', hmm', hm'm, hstm, hmd, hm'd, hraise, hsub⟩ :=
    _root_.GlobalTheory.WeightPart.exists_weightPart (adjA σ J) (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)))
      (wt d (∑ i, d i + 1)) (Option.map Sum.swap) hm hi hε hτ hw hττ _ _ hxy1 hyx1 (adjA_mat hJ p)
      (_root_.GlobalTheory.UAut.NoLower.parFlag_no_lower F E σ h n J hJ r X Y d _ hdM hxx hyy hxy p hp)
      (_root_.GlobalTheory.UAut.NoLower.parFlag_no_lower F E σ h n J hJ r X Y d _ hdM hxx hyy hxy p⁻¹ (inv_mem hp))
  let U : GL (Fin n) (AF F ⊗[F] E) := ⟨m, m', hmm', hm'm⟩
  have hU : U ∈ HR (AF F) σ J := (adjA_mul_self_iff hJ U).1 (by
    show adjA σ J m * m = 1
    rw [hstm, hm'm])
  let g : GAd σ J := (⟨U, hU⟩ : HR (AF F) σ J)
  have hg1 : (matHom _ σ J g).1 = m := rfl
  have hg2 : (matHom _ σ J g⁻¹).1 = m' := by
    rw [map_inv]
    rfl
  have hgl : g ∈ leviFlag σ J X Y d :=
    _root_.GlobalTheory.UAut.mem_leviFlag_of_keeps_weights F E σ h n J hJ r X Y d _ hdM hxx hyy hxy g (by rw [hg1]; exact hmd) (by rw [hg2]; exact hm'd)
  refine ⟨p * g⁻¹, ?_, g, hgl, (inv_mul_cancel_right p g).symm, ?_⟩
  · rw [mem_unipFlag_iff_raise hJ hσ X _ hL hxx hLL hdM, map_mul, Units.val_mul, hg2]
    exact hraise
  · intro hpr
    rw [← range_ratEmb σ J] at hpr
    obtain ⟨γ, hγ⟩ := hpr
    have : Nontrivial (AF F) := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      exact (evInf F w).toRingHom.domain_nontrivial
    have hinj : Function.Injective (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E) :=
      Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap F (AF F)))
    have hφ : Function.Injective ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix :
        Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := Matrix.map_injective hinj
    have hu : ∀ j, idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range :=
      fun j => ⟨_, rfl⟩
    have hsu : ∀ j, adjA σ J (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J) j) ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      intro j
      show adjA σ J ((X * Matrix.single j j (1 : E) * (Formalism.UG.cT (σ : E →+* E) Y * J)).map
        (inclR (F := F) (AF F))) ∈ _
      rw [adjA_map]
      exact ⟨_, rfl⟩
    have hε0 : ∀ a, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      rintro (_ | j | j)
      · exact Subring.sub_mem _ (Subring.one_mem _) (Subring.sum_mem _ fun j _ => by
          rcases j with j | j
          exacts [hu j, hsu j])
      · exact hu j
      · exact hsu j
    have hx0 : (matHom _ σ J p).1 ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      rw [← hγ]
      exact ⟨_, rfl⟩
    have hy0 : (matHom _ σ J p⁻¹).1 ∈
        ((inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix : Matrix (Fin n) (Fin n) E →+* _).range := by
      rw [← hγ, ← map_inv]
      exact ⟨_, rfl⟩
    obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ := hsub _ hε0 hx0 hy0
    have hkk' : k * k' = 1 := hφ (by rw [map_mul, map_one, hk, hk', hmm'])
    have hk'k : k' * k = 1 := hφ (by rw [map_mul, map_one, hk, hk', hm'm])
    have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
    have hadj : J⁻¹ * Formalism.UG.cT (σ : E →+* E) k * J = k' := hφ (by
      show (J⁻¹ * Formalism.UG.cT (σ : E →+* E) k * J).map (inclR (F := F) (AF F)) = _
      rw [← adjA_map, hk', ← hstm, ← hk]
      rfl)
    have hUJ : Formalism.UG.cT (σ : E →+* E) k * J * k = J := by
      calc Formalism.UG.cT (σ : E →+* E) k * J * k = J * (J⁻¹ * Formalism.UG.cT (σ : E →+* E) k * J) * k := by
            rw [← mul_assoc J, ← mul_assoc J, Matrix.mul_nonsing_inv _ hdet, one_mul]
        _ = J := by rw [hadj, mul_assoc, hk'k, mul_one]
    let K : GL (Fin n) E := ⟨k, k', hkk', hk'k⟩
    have hK : K ∈ Formalism.UG.UJ (σ : E →+* E) J := by
      show Formalism.UG.cT (σ : E →+* E) k * J * k = J
      exact hUJ
    rw [← range_ratEmb σ J]
    refine ⟨⟨K, hK⟩, matHom_injective _ σ J (Units.ext ?_)⟩
    show (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).mapMatrix k = m
    exact hk

private theorem unipFlag_inf_leviFlag_eq_bot (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ)
    (hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0) (hyy : Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0)
    (hxy : Formalism.UG.cT (σ : E →+* E) X * J * Y = 1) :
    unipFlag σ J X d ⊓ leviFlag σ J X Y d = ⊥ := by
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma h
  obtain ⟨hL, hLL⟩ := cT_Y_J_X_eq_one_and_complement_eq_zero σ hJ hσ hyy hxy
  have hdM : ∀ j, d j < ∑ i, d i + 1 := fun j =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  have hε : CompleteOrthogonalIdempotents (fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J))) :=
    idemA_complete hJ X _ hL hxx hLL
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨hu, hl⟩ := Subgroup.mem_inf.1 hg
  have hl' : g ∈ parFlag σ J X d ⊓ parFlag σ J Y d := hl
  rw [mem_unipFlag_iff_raise hJ hσ X _ hL hxx hLL hdM] at hu
  have hu' : ∀ a b, wt d (∑ i, d i + 1) a ≤ wt d (∑ i, d i + 1) b + ((0 : ℕ) : ℤ) →
      fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * ((matHom _ σ J g).1 - 1) *
        fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := hu
  have hY := _root_.GlobalTheory.UAut.OppFlagWeight.not_raise_of_mem_parFlag F E σ h n J hJ r X Y d _ hdM hxx hyy hxy g (Subgroup.mem_inf.1 hl').2
  have hz : ∀ a b, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * ((matHom _ σ J g).1 - 1) *
      fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
    intro a b
    by_cases hab : wt d (∑ i, d i + 1) a ≤ wt d (∑ i, d i + 1) b
    · exact hu' a b (by simpa using hab)
    · rw [not_le] at hab
      have hne : a ≠ b := by
        rintro rfl
        exact lt_irrefl _ hab
      rw [mul_sub, sub_mul, hY a b hab, mul_one, hε.ortho hne, sub_zero]
  have h0 : (matHom _ σ J g).1 - 1 = 0 := by
    rw [show (matHom _ σ J g).1 - 1 =
        (∑ a, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a) * ((matHom _ σ J g).1 - 1) *
          (∑ b, fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b) by
        rw [hε.complete, one_mul, mul_one]]
    simp only [Finset.sum_mul, Finset.mul_sum, hz, Finset.sum_const_zero]
  apply matHom_injective _ σ J
  rw [map_one]
  exact Units.ext (sub_eq_zero.1 h0)

theorem levi_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → (∀ p ∈ parFlag σ J X d, ∃ u ∈ unipFlag σ J X d, ∃ m ∈ leviFlag σ J X Y d, p = u * m ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J)) ∧ unipFlag σ J X d ⊓ leviFlag σ J X Y d = ⊥ ∧ leftGrp σ J X d = unipFlag σ J X d ⊔ (ratPts σ J ⊓ leviFlag σ J X Y d) ∧ ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y d hxx hyy hxy
  refine ⟨fun p hp => exists_unipFlag_mul_leviFlag_eq_of_mem_parFlag F E σ h n J hJ r X Y d hxx hyy hxy p hp,
    unipFlag_inf_leviFlag_eq_bot F E σ h n J hJ r X Y d hxx hyy hxy, ?_,
    fun t a ht hta => _root_.GlobalTheory.UAut.TorusLevi.torus_mem_leviFlag F E σ h n J hJ r X Y d hxx hyy hxy t a ht hta⟩
  apply le_antisymm
  · show unipFlag σ J X d ⊔ (ratPts σ J ⊓ parFlag σ J X d) ≤ _
    refine sup_le le_sup_left ?_
    intro p hp
    obtain ⟨hpr, hpp⟩ := Subgroup.mem_inf.1 hp
    obtain ⟨u, hu, m, hm, hpe, hrat⟩ := exists_unipFlag_mul_leviFlag_eq_of_mem_parFlag F E σ h n J hJ r X Y d hxx hyy hxy p hpp
    rw [hpe]
    exact Subgroup.mul_mem_sup hu (Subgroup.mem_inf.2 ⟨hrat hpr, hm⟩)
  · show _ ≤ unipFlag σ J X d ⊔ (ratPts σ J ⊓ parFlag σ J X d)
    exact sup_le_sup_left (inf_le_inf_left _ (inf_le_left : parFlag σ J X d ⊓ parFlag σ J Y d ≤ _)) _

end GlobalTheory.LeviFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsGaloisCompat
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GeomFrobChar


open GlobalTheory.WeilDeligne Polynomial in
theorem charpoly_geomFrob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (B : ValuationSubring Ω) (h : IsPlaceOver B w)
      (rc : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h), GlobalTheory.LocLanglands.IsRec h rc →
    ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ S →
    ∀ t : ℝ, GlobalTheory.WeilDeligne.wdOf h hl ι r = (rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw t →
    ∀ g : G E Ω, IsFrob (F := E) B (normV w) g →
      (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
        Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ)))).prod := by
  intro E Ω _ _ _ _ _ l _ ι a r hr w hl B h rc hrc σ S hS t hw g hg
  obtain ⟨α, rfl, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ S).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hS⟩)
  have e := ParLaws.rec_eq_diag hrc (σ := ParLaws.toRep σ) hα
  let φ : Weil h := ⟨g, mem_Weil_of_isFrob h hg⟩
  have hφ : deg φ = 1 := deg_eq_one_iff.mpr hg
  have h1 := charPol_wdOf hl ι (Units.continuous_val.comp hr) φ⁻¹
  have e' : rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := e
  have h2 : ((WDRep.diag h fun i => (α i)⁻¹).tw t).ρ φ⁻¹ =
      diagEnd fun i => (α i : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    rw [WDRep.tw_ρ, WDRep.diag_ρ, deg_inv, hφ, Complex.ofReal_neg, Complex.cpow_neg]
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply, mul_assoc, mul_left_comm]
  rw [hw, e', WD.lpTw_mk, WD.charPol_mk, h2, charpoly_diagEnd] at h1
  apply Polynomial.map_injective ι.toRingHom ι.injective
  rw [zpow_neg_one]
  refine (show _ = _ from h1.symm).trans ?_
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp

end GlobalTheory.GeomFrobChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LatMulAd

variable {D : D7}

theorem mulVec_map_mem_hatL {n : ℕ} (g : Matrix (Fin n) (Fin n) D.host.E)
    (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hg : ∀ x ∈ Λ, g *ᵥ x ∈ Λ') (y : Fin n → EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    g.map (eToEAf D) *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨g *ᵥ x, hg x hx, ?_⟩
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul r a _ ha =>
    have : g.map (eToEAf D) *ᵥ (r • a) = r • (g.map (eToEAf D) *ᵥ a) := by
      show _ = (r : EAf D) • (g.map (eToEAf D) *ᵥ a)
      rw [← Matrix.mulVec_smul]
      rfl
    rw [this]; exact Submodule.smul_mem _ r ha

theorem mem_hatL_colLat_mul (D : D7) {n : ℕ} (γ B : GL (Fin n) D.host.E) : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (γ * B)) ↔
      (γ⁻¹).1.map (eToEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) := by
  intro v
  have h1 : ∀ x ∈ colLat B, (γ : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x ∈ colLat (γ * B) := by
    intro x hx
    rw [colLat_mul]
    exact ⟨x, hx, rfl⟩
  have h2 : ∀ x ∈ colLat (γ * B), ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x ∈ colLat B := by
    intro x hx
    rw [colLat_mul] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ ((γ : Matrix (Fin n) (Fin n) D.host.E) *ᵥ y) ∈ _
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy
  constructor
  · intro hv
    exact mulVec_map_mem_hatL _ _ _ h2 v hv
  · intro hv
    have := mulVec_map_mem_hatL _ _ _ h1 _ hv
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec] at this

end GlobalTheory.LatMulAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodProjLevel

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G]

theorem mem_levi_flag_of_mem_parabolic (P : LevelP L.Pg L.r ℂ) {k : GA D V} (hk : k ∈ levG V β (flag1L L)) :
    k ∈ levG V β (withP L P) ∧ levChi V β (withP L P) k = levChi V β (flag1L L) k := by
  have h1 : rTup β L (finE V k) = 1 := by
    have : rTup β L (finE V k) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := hk.2.2
    exact Subgroup.mem_bot.1 this
  refine ⟨⟨hk.1, hk.2.1, ?_⟩, ?_⟩
  · show rTup β L (finE V k) ∈ P.H
    rw [h1]; exact P.H.one_mem
  · unfold levChi
    rw [levFn_withP, h1, blockDiagonalExtendByOnePrimeField_one, one_mul, levFn_flag1]

theorem isPLevel_of_hasType (hL : LiftsExist V β L) {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ}
    (hF : HasType V β (withP L P) F) : IsPLevel V β L P F := by
  have h1 : HasType V β (flag1L L) F := fun k hk h => by
    rw [hF k (mem_levi_flag_of_mem_parabolic P hk).1, (mem_levi_flag_of_mem_parabolic P hk).2]
  refine ⟨h1, fun p => ?_⟩
  obtain ⟨κ, hκ⟩ := hL p.1
  have hp : rTup β L (finE V κ) ∈ P.H := by rw [hκ.2.2]; exact p.2
  have hm : κ ∈ levG V β (withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
  have hc : levChi V β (withP L P) κ = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) κ := by
    unfold levChi
    rw [levFn_withP, hκ.2.2, extendOne_of_mem _ p.2, Units.val_mul]
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  funext h
  rw [level_action_spec h1 ⟨κ, hκ⟩ κ hκ h, hF κ hm, hc]
  field_simp

theorem postOn_actL_mem (g0 : G0 L.Pg L.r) {X : MMap M}
    (hT : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (actL V β L g0) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  have hU : ∀ v, postOn M (actL V β L g0) X v = actG0 V β L g0 (X v) := fun _ => rfl
  by_cases hex : ∃ κ, IsLevelLift V β L g0 κ
  · have hκ := hex.choose_spec
    have e : postOn M (actL V β L g0) X = (levChi V β (flagL L) hex.choose)⁻¹ • heckeOn M {hex.choose} X := by
      ext v g
      rw [hU, actG0, dite_eq_left hex]
      simp [heckeOn, postOn_apply, heckeLin_apply]
    rw [e]
    refine Submodule.smul_mem _ _ ?_
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
    refine GlobalTheory.SphericalOps.isMultMap_heckeOn hT (fun k hk => ?_) fun v k hk g => ?_
    · rw [Finset.mem_singleton.1 hk]
      exact hκ.1
    · obtain ⟨h1, h2⟩ := GlobalTheory.FlagAction.conj_mem_flag1 hκ hk
      simp only [heckeLin_apply, Finset.sum_singleton]
      rw [← h2, ← hT.lev v _ h1]
      group
  · have e : postOn M (actL V β L g0) X = 0 := by
      ext v g
      rw [hU, actG0, dite_eq_right hex]
      rfl
    rw [e]
    exact zero_mem _

theorem postOn_gaL_mem_goodPart (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g)
    (hcomm : ∀ g F, HasType V β (flag1L L) F →
      gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F))
    (P : LevelP L.Pg L.r ℂ) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (withP L P) : Set (GA D V)) (levChi V β (withP L P))) :
    postOn M (gaL V β L eG c) X ∈
      goodPart θ M (levG V β (withP L P) : Set (GA D V)) (levChi V β (withP L P)) (gaL V β L eG c) := by
  have hX1 : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) :=
    GlobalTheory.ProjectedLift.mult_mono (fun k hk => mem_levi_flag_of_mem_parabolic P hk) hX
  have hY : postOn M (gaL V β L eG c) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
    have e : postOn M (gaL V β L eG c) X = ∑ g, c g • postOn M (actL V β L (eG g)) X := by
      ext v h
      simp [gaL, postOn_apply]
    rw [e]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (postOn_actL_mem _ hX1)
  rw [mem_goodPart]
  refine ⟨?_, fun v => GlobalTheory.ProjectedLift.gaL_gaL hL eG c hc (GlobalTheory.hasType_of_mem_mult θ M β _ X hX1 v)⟩
  have hY' := (GlobalTheory.MultMem.mem_mult_iff ..).1 hY
  refine (GlobalTheory.MultMem.mem_mult_iff ..).2 ⟨hY'.aut, hY'.cusp, fun v => ?_, hY'.equiv, hY'.cont⟩
  have hP := isPLevel_of_hasType hL (GlobalTheory.hasType_of_mem_mult θ M β _ X hX v)
  have hQ : IsPLevel V β L P (gaL V β L eG c (X v)) := by
    refine ⟨hY'.lev v, fun p => ?_⟩
    have e1 : actL V β L p.1 (X v) = ((P.chi p : ℂˣ) : ℂ) • X v := hP.2 p
    have e2 := hcomm (eG.symm p.1) _ hP.1
    rw [MulEquiv.apply_symm_apply, e1, map_smul] at e2
    exact e2.symm
  exact hQ.hasType

end Act

theorem proj_mem_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_record → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ), ∀ U ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)), postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) U ∈ R.Wat i (sg0 D A) P := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h hr hv i P U hU
  have hL : LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
    obtain ⟨c, hc⟩ := h.βW i
    refine GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_) (Finset.disjoint_empty_right _)
    obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    obtain ⟨k', hk'⟩ := (h.Pg PP').1 (hP'.resolve_right (Finset.notMem_empty _))
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ hv
  have hc : ∀ g, ∑ a, RealDat.eC (A := A) (sg0 D A) a * RealDat.eC (A := A) (sg0 D A) (a⁻¹ * g) =
      RealDat.eC (A := A) (sg0 D A) g := by
    rw [hs]; exact GlobalTheory.ProjectedLift.eC_conv R hr
  exact postOn_gaL_mem_goodPart (L := R.datWp i R.triv) hL R.eG _ hc
    ((GlobalTheory.ProjComm.proj_comm R h hr).2 i (sg0 D A)) P hU

end GlobalTheory.GoodProjLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesOfPointLocalRingLeSeparatedStatement
section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specializes_of_pointLocalRing_le_separated : ∀ (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated] (x z : X), locRing x ≤ locRing z → z ⤳ x := by
  first | exact @GlobalTheory.specializes_of_locRing_le | exact GlobalTheory.specializes_of_locRing_le | (intros; apply GlobalTheory.specializes_of_locRing_le <;> assumption)
end

