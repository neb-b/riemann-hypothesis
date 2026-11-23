module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDet
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0370
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1157
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdeleMapMemIntAdIff
section
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing TensorProduct
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.RgEisBInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_below_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ w : HeightOneSpectrum (𝓞 E), below F w = v := by
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 E)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (hker.le.trans bot_le)
  have hne : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact hker
  exact ⟨⟨Q, hQ, hne⟩, HeightOneSpectrum.ext hQv⟩

theorem adeleMap_mem_intAd_iff (x : 𝔸[F]) : adeleMap F E x ∈ intAd E ↔ x ∈ intAd F := by
  have key : ∀ w : HeightOneSpectrum (𝓞 E),
      finEval w (adeleMap F E x) ∈ w.adicCompletionIntegers E ↔
        finEval (below F w) x ∈ (below F w).adicCompletionIntegers F := by
    intro w
    haveI := liesOver_below (K := F) w
    haveI := w.isPrime
    have h1 : finEval w (adeleMap F E x) =
        SemiLocal.completionMap (below F w) w (finEval (below F w) x) :=
      finiteAdeleMap_apply x.2 w
    rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      SemiLocal.valued_completionMap]
    exact pow_le_one_iff (Ideal.ramificationIdx_pos (R := 𝓞 F) w.asIdeal).ne'
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  constructor
  · intro h v
    obtain ⟨w, rfl⟩ := exists_below_eq (E := E) v
    exact (key w).1 (h w)
  · intro h w
    exact (key w).2 (h _)

theorem nuCM_eqv (x : 𝔸[F]) : eqv F E (nuCM F E x) = adeleMap F E x := by
  have h := (GroundTheory.BlockD.ThmBHecke.adeleEquiv F E).commutes x
  exact h

theorem bInt : BInt := by
  unfold BInt ForCM
  intro F E _ _ _ _ _ σ χ c _ _ _ _ x
  simp only [adCM, Subring.mem_comap]
  change eqv F E (nuCM F E x) ∈ intAd E ↔ _
  rw [nuCM_eqv, adeleMap_mem_intAd_iff]

end GlobalTheory.CompanionTheory.RgEisBInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapHalfTr
section
open PositivityTheory.RgEis PositivityTheory.RgEis.So

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisFix

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_conj (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [hτ, hτ, star_star]

theorem exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  obtain ⟨-, hC, -, hτ⟩ := h
  by_contra hno
  push Not at hno
  let τ : E →+* ℂ := Classical.arbitrary _
  have hR : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    exact ((hτ τ x).symm.trans (congrArg τ (hno x)) : _)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (hC.isComplex (InfinitePlace.mk τ)))
    (InfinitePlace.isReal_mk_iff.2 hR)

theorem add_conj_mem (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) :
    ∃ c : F, e + σ e = algebraMap F E c := by
  let S : Submodule F E := LinearMap.eqLocus σ.toLinearMap LinearMap.id
  have hS : S ≠ ⊤ := by
    obtain ⟨y, hy⟩ := exists_moved σ h
    intro hT
    have hyS : y ∈ S := hT ▸ Submodule.mem_top
    exact hy hyS
  have h1 : Submodule.span F {(1 : E)} ≤ S := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact map_one σ
  have hlt : Module.finrank F S < 2 := h.2.2.1 ▸ Submodule.finrank_lt hS
  have hone : Module.finrank F (Submodule.span F {(1 : E)}) = 1 :=
    finrank_span_singleton one_ne_zero
  have heq : Submodule.span F {(1 : E)} = S :=
    Submodule.eq_of_le_of_finrank_le h1 (by omega)
  have hmem : e + σ e ∈ S := by
    change σ (e + σ e) = e + σ e
    rw [map_add (f := _), conj_conj σ h, add_comm]
  rw [← heq, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩

def halfTr (σ : E →ₐ[F] E) : E →ₗ[F] F :=
  (4⁻¹ : F) • (Algebra.trace F E ∘ₗ (LinearMap.id + σ.toLinearMap))

theorem algebraMap_halfTr (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (halfTr σ e) = (2⁻¹ : F) • (e + σ e) := by
  obtain ⟨c, hc⟩ := add_conj_mem σ h e
  have hval : halfTr σ e = 2⁻¹ * c := by
    simp only [halfTr, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, smul_eq_mul]
    rw [hc, Algebra.trace_algebraMap, h.2.2.1, nsmul_eq_mul]
    push_cast
    ring
  rw [hval, hc, Algebra.smul_def, map_mul]

theorem halfTr_one (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : halfTr σ (1 : E) = 1 := by
  apply (algebraMap F E).injective
  rw [algebraMap_halfTr σ h, map_one, map_one, Algebra.smul_def, map_inv₀, map_ofNat]
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  field_simp
  norm_num

def rr (σ : E →ₐ[F] E) : AE F E →ₗ[AF F] AF F :=
  (TensorProduct.AlgebraTensorModule.rid F (AF F) (AF F)).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.lTensor (AF F) (AF F) (halfTr σ)

theorem rr_tmul (σ : E →ₐ[F] E) (a : AF F) (e : E) : rr σ (a ⊗ₜ[F] e) = halfTr σ e • a := by
  simp [rr]

theorem nu_apply (x : AF F) : nuCM F E x = x ⊗ₜ[F] (1 : E) := rfl

theorem rr_nu (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : AF F) : rr σ (nuCM F E x) = x := by
  rw [nu_apply, rr_tmul, halfTr_one σ h, one_smul]

theorem cA_nu (σ : E →ₐ[F] E) (x : AF F) : cA σ (nuCM F E x) = nuCM F E x := by
  simp [nu_apply, cA]

theorem nu_rr (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (z : AE F E) :
    nuCM F E (rr σ z) = (2⁻¹ : F) • (z + cA σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), ← smul_add]
    congr 1
    abel
  | tmul a e =>
    have hc : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [cA]
    rw [rr_tmul, nu_apply, hc, ← TensorProduct.tmul_add, ← TensorProduct.tmul_smul,
      ← algebraMap_halfTr σ h, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']

theorem continuous_nu : Continuous (nuCM F E) := by
  have h : (nuCM F E : AF F → AE F E) = fun x => x • (1 : AE F E) := by
    funext x
    rw [nu_apply, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact Continuous.smul (f := fun x : AF F => x) (g := fun _ => (1 : AE F E)) continuous_id continuous_const

theorem bFix : BFix := by
  intro F E _ _ _ _ _ σ χ c hCM _ _ _
  refine ⟨continuous_nu, Function.LeftInverse.injective (rr_nu σ hCM), cA_nu σ, rr σ,
    IsModuleTopology.continuous_of_linearMap (rr σ), fun x hx => ?_⟩
  have hx' : cA σ x = x := hx
  rw [nu_rr σ hCM, hx', ← two_smul F x, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

end GlobalTheory.CompanionTheory.RgEisFix
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BaseCM
section
open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.CompanionTheory.SgOneBase

theorem baseCM : CMGood → BFix → BRat → BInt → BInf → BLg → BDel → BaseCM := by
  intro _ hFix hRat hInt hInf hLg hDel F E _ _ _ _ _ σ χ c hCM hUn hHk hRes ε
  obtain ⟨hνc, hνi, hνfix, r, hrc, hrfix⟩ := hFix F E σ χ c hCM hUn hHk hRes
  obtain ⟨hrat, hrat'⟩ := hRat F E σ χ c hCM hUn hHk hRes
  have hint := hInt F E σ χ c hCM hUn hHk hRes
  obtain ⟨hinf, hinf'⟩ := hInf F E σ χ c hCM hUn hHk hRes
  obtain ⟨hlg, hlgσ⟩ := hLg F E σ χ c hCM hUn hHk hRes
  obtain ⟨δ0, α0, u0, hσδ, hδα, huO, huiO, hun⟩ := hDel F E σ χ c hCM hUn hHk hRes
  have hσi : ∀ x : E, (adCM σ χ).σ ((adCM σ χ).i x) = (adCM σ χ).i (σ x) := by
    intro x
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (σ x)
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  let f : IdeleGroup F →* Circle := χ.comp (Units.map (nuCM F E).toMonoidHom)
  have hker : (IdeleGroup.diagonal F).range ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    have e : Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a) =
        Units.map (inclR (F := F) (E := E) (AF F) : E →* TensorProduct F (AF F) E) (Units.map (algebraMap F E : F →* E) a) :=
      Units.ext (hrat a)
    show χ (Units.map (nuCM F E).toMonoidHom (IdeleGroup.diagonal F a)) = 1
    rw [e]
    exact hHk.2 _
  have hfc : Continuous f := hHk.1.comp (Continuous.units_map _ hνc)
  let ω : HeckeCharacter F :=
    ⟨QuotientGroup.lift _ f hker, (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 hfc⟩
  have hω : ∀ x : IdeleGroup F, ω.toIdele x = (adCM σ χ).χ (Units.map (nuCM F E).toMonoidHom x) := fun x => rfl
  rcases Int.units_eq_one_or ε with rfl | rfl
  · refine ⟨r, δ0, α0, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_,
      ⟨u0, hδα, huO, huiO, hun⟩, hω⟩⟩
    rw [hσi, hσδ, map_neg]
    simp
  · refine ⟨r, 1, 1, ω, ⟨hνc, hνi, hνfix, hrc, hrfix, hrat, hrat', hint, hinf, hinf', hlg, hlgσ, ?_,
      ⟨1, ?_, ?_, ?_, ?_⟩, hω⟩⟩
    · simp
    · simp
    · simpa using (adCM σ χ).O.one_mem
    · simpa using (adCM σ χ).O.one_mem
    · intro w
      simp

end GlobalTheory.CompanionTheory.SgOneBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDetParabolicFrame
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrameDet

theorem mul_fromRows_apply {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
    (M : Matrix (β ⊕ β) (β ⊕ β) R) (C : Matrix (β ⊕ β) β R) (hC : C = Matrix.fromRows (1 : Matrix β β R) 0)
    (i : β ⊕ β) (j : β) : (M * C : Matrix (β ⊕ β) β R) i j = M i (Sum.inl j) := by
  subst hC
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem corner_conj {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
    (B P Bi : Matrix (β ⊕ β) (β ⊕ β) R) (T Ti s : Matrix β β R) (C D : Matrix (β ⊕ β) β R)
    (hC : C = Matrix.fromRows (1 : Matrix β β R) 0)
    (hBi : Bi * B = 1) (hTi : T * Ti = 1)
    (hB : (B * C : Matrix (β ⊕ β) β R) = (D * T : Matrix (β ⊕ β) β R))
    (hP : (P * D : Matrix (β ⊕ β) β R) = (D * s : Matrix (β ⊕ β) β R)) (r c : β) :
    (Bi * P * B) (Sum.inl r) (Sum.inl c) = (Ti * s * T) r c := by
  have hD : D = B * C * Ti := by rw [hB, Matrix.mul_assoc, hTi, Matrix.mul_one]
  have key : Bi * P * B * C = C * (Ti * s * T) := by
    calc Bi * P * B * C = Bi * ((P * D) * T) := by
          rw [Matrix.mul_assoc (Bi * P) B C, hB]; simp only [Matrix.mul_assoc]
      _ = Bi * (D * s * T) := by rw [hP]
      _ = Bi * (B * C * Ti * s * T) := by rw [← hD]
      _ = (Bi * B) * C * (Ti * s * T) := by simp only [Matrix.mul_assoc]
      _ = C * (Ti * s * T) := by rw [hBi, Matrix.one_mul]
  have h1 := congrFun (congrFun key (Sum.inl r)) c
  rw [mul_fromRows_apply _ C hC] at h1
  rw [h1, hC, Matrix.fromRows_mul, Matrix.fromRows_apply_inl, Matrix.one_mul]

theorem bdet_frameEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E), b.1.toCols₁ = diagCols (Fin n) * t₀.1 → ∀ (p : G2 σ Y) (t : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), IsPar p t → bdet (Sum.inl '' (Set.univ : Set (Fin n))) (frameEquiv χ ε b hb p).1 = Matrix.GeneralLinearGroup.det t := by
  intro F E _ _ _ _ _ σ n Y χ ε b hb t₀ ht₀ p t hp
  obtain ⟨t₀A, ht₀A⟩ : ∃ g : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      g = Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t₀ := ⟨_, rfl⟩
  have hent : ∀ r c : Fin n, (((frameEquiv χ ε b hb p).1 : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (Sum.inl r) (Sum.inl c) =
      ((t₀A⁻¹ * t * t₀A : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) r c := by
    intro r c
    rw [frameEquiv_val]
    simp only [Units.val_mul]
    refine corner_conj _ _ _ _ _ _ _ _ rfl (Units.inv_mul _) (Units.mul_inv _) ?_ hp r c
    refine Matrix.ext fun i j => ?_
    rw [mul_fromRows_apply _ _ rfl, bA_val]
    have hij := congrFun (congrFun ht₀ i) j
    rw [Matrix.toCols₁_apply] at hij
    subst ht₀A
    show inclR (F := F) (E := E) (AF F) (b.1 i (Sum.inl j)) = _
    rw [hij]
    cases i with
    | inl r' =>
      show inclR (F := F) (E := E) (AF F)
        (∑ k, Matrix.fromRows (1 : Matrix (Fin n) (Fin n) E) 1 (Sum.inl r') k * t₀.1 k j) = _
      simp [diagCols, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
    | inr r' =>
      show inclR (F := F) (E := E) (AF F)
        (∑ k, Matrix.fromRows (1 : Matrix (Fin n) (Fin n) E) 1 (Sum.inr r') k * t₀.1 k j) = _
      simp [diagCols, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
  rw [GlobalTheory.CompanionTheory.RgEisLevi.bdet_inl Set.univ _ (t₀A⁻¹ * t * t₀A) hent, GlobalTheory.CompanionTheory.RgEis.bdet_univ,
    map_mul, map_mul, mul_comm, ← mul_assoc, map_inv, mul_inv_cancel, one_mul]

end GlobalTheory.CompanionTheory.SiegelFrameDet
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Brat
section
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisBrat

open scoped TensorProduct NumberField.AdeleRing
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

theorem brat : BRat := by
  intro F E _ _ _ _ _ σ χ c _ _ _ _
  refine ⟨fun y => ?_, fun e x h => ?_⟩
  · change (algebraMap F (AF F) y) ⊗ₜ[F] (1 : E) = (1 : AF F) ⊗ₜ[F] (algebraMap F E y)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · obtain ⟨g, hg⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F E))
    have g1 : g 1 = 1 := by
      have := LinearMap.congr_fun hg (1 : F)
      simpa using this
    have h' : (1 : AF F) ⊗ₜ[F] e = x ⊗ₜ[F] (1 : E) := h
    have h2 := congrArg (fun t => TensorProduct.rid F (AF F) (LinearMap.lTensor (AF F) g t)) h'
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, g1, one_smul] at h2
    refine ⟨g e, ?_⟩
    rw [← h2, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.CompanionTheory.EisBrat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardResidueEqQV
section
noncomputable section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JacEigAt

theorem qV_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : 0 < qV E w := by
  unfold qV
  exact Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem card_residue_eq_qV {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Nat.card 𝓀[w.adicCompletion E] = qV E w := by
  have h := GlobalTheory.LocLanglands.resCard_eq_normV (w := w)
  simpa [GlobalTheory.SplitWeil.resCard, Formalism.ConjugateSelfDual.normV, qV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

theorem modExp_points (n : ℕ) (a : Fin n) :
    modExp (fun _ : Fin n => Unit) a = (n : ℤ) - 1 - 2 * (a : ℕ) := by
  have h1 : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
  have h2 : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
  have ha := a.2
  simp only [modExp, Fintype.card_unique, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one, h1, h2,
    Fin.card_Ioi, Fin.card_Iio]
  omega

theorem nabs_zpow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (h : ord k ϖ = 1) (m : ℤ) :
    GlobalTheory.SplitWeil.nabs k (ϖ ^ m) = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) := by
  have h1 : GlobalTheory.SplitWeil.nabs k (ϖ ^ m) = GlobalTheory.SplitWeil.nabs k ϖ ^ m := by
    simp [GlobalTheory.SplitWeil.nabs]
  rw [h1, GlobalTheory.LGrp.nabs_eq_zpow, h, _root_.zpow_neg, zpow_one, _root_.inv_zpow, _root_.zpow_neg]

theorem prod_zpow_sum {ι : Type} (s : Finset ι) (r : ℂ) (hr : r ≠ 0) (f : ι → ℤ) :
    ∏ a ∈ s, r ^ f a = r ^ ∑ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hr]

theorem absPow_term {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ord (w.adicCompletion E) ϖ = 1) (e m : ℤ) :
    (absPow (w.adicCompletion E) ((e : ℂ) / 2) (ϖ ^ m) : ℂ) =
      (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (-(e * m)) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  set r : ℝ := Real.sqrt (qV E w : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hq
  have hrq : (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = r ^ (2 : ℤ) := by
    have : (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = qV E w := by
      simp [GlobalTheory.SplitWeil.resCard, card_residue_eq_qV]
    rw [this, hr, zpow_ofNat, Real.sq_sqrt hq.le]
  have hs : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hs, val_absPow_ofReal, nabs_zpow ϖ h, hrq, ← _root_.zpow_mul, ← Real.rpow_intCast, ← Real.rpow_mul hr0.le]
  have : (((2 * -m : ℤ) : ℝ)) * ((e : ℝ) / 2) = ((-(e * m) : ℤ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_intCast]
  push_cast
  rfl

theorem deltaHalf_inv {E : Type} [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ord (w.adicCompletion E) ϖ = 1) (x : Fin n → ℤ) :
    (((deltaHalf (w.adicCompletion E) (fun _ : Fin n => Unit)
        (leviTorus (w.adicCompletion E) (Fin n) fun i => ϖ ^ x i))⁻¹ : ℂˣ) : ℂ) =
      (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  have hr : (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hd : ∀ i, GeneralLinearGroup.det
      (leviTorus (w.adicCompletion E) (Fin n) (fun i => ϖ ^ x i) i) = ϖ ^ x i :=
    fun i => congrFun ((leviTorus (w.adicCompletion E) (Fin n)).left_inv fun i => ϖ ^ x i) i
  rw [Units.val_inv_eq_inv_val, deltaHalf_apply, Units.coe_prod]
  simp only [hd, absPow_term w ϖ h, modExp_points]
  rw [prod_zpow_sum _ _ hr, ← _root_.zpow_neg, Finset.sum_neg_distrib, neg_neg]

end GlobalTheory.CompanionTheory.JacEigAt


end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExists
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWCoef

theorem coefDataExists : PositivityTheory.PfSWUS.CoefDataExists := by
  intro D n
  have h : ∀ b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n, ∃ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b.1 0 1 :=
    fun b => (GlobalTheory.StdUnn.Model.exists_unip _).2 b.2
  choose nb hnb using h
  obtain ⟨lam, 𝓖, hl⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D n
  exact ⟨nb, lam, 𝓖, hnb, hl⟩

end GlobalTheory.CompanionTheory.SWCoef

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityZeroOfSplitColumnStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_cell_multiplicity_zero_of_split_column : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h r : ℕ} (x : Fin h → IrrGL (k := k)) (y : Fin r → IrrGL (k := k)), (∀ j, (y j).IsCusp) → ∀ (b : Fin h → Fin r → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (y j).1) (j : Fin r) (i i' : Fin h), i ≠ i' → b i j ≠ 0 → b i' j ≠ 0 → jhMult (piTensor fun j => (y j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.CellMulti.jhMult_cell_eq_zero | exact GlobalTheory.CompanionTheory.FineProd.CellMulti.jhMult_cell_eq_zero | (intros; apply GlobalTheory.CompanionTheory.FineProd.CellMulti.jhMult_cell_eq_zero <;> assumption)
end

