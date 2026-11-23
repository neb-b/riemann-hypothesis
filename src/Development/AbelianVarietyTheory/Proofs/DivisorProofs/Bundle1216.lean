module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0999
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithGlobalMaximumPrincipleOffDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem max_principle_global : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ (N : ℕ) (f : X.functionField) (R : ℝ), f ∈ P.H N 0 → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ρ ≤ P.nu 0 1 σ y s → P.nu N 0 σ y f ≤ R) → f ∈ P.Bl N 0 (Real.exp (δ * N) * R) := by
  intro k _ X _ p D hX P s hs hs0 δ hδ
  classical
  choose W ρ hW hρ H using _root_.GlobalTheory.VolBr.Pair.max_principle_near k X p D hX P s hs hs0 δ hδ
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  have hcov : ∀ σ : k →+* ℂ, ∃ t : Finset (CxPts p σ), (Set.univ : Set (CxPts p σ)) ⊆ ⋃ x ∈ t, W σ x := by
    intro σ
    haveI : CompactSpace (CxPts p σ) := hX.compactSpace σ
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (W σ) (fun x _ => hW σ x)
    exact ⟨t, ht⟩
  choose t ht using hcov
  have hlow : ∀ {ι : Type} [Finite ι] (g : ι → ℝ), (∀ i, 0 < g i) → ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ g i := by
    intro ι _ g hg
    rcases isEmpty_or_nonempty ι with h | h
    · exact ⟨1, one_pos, fun i => (h.false i).elim⟩
    · obtain ⟨i, hi⟩ := Finite.exists_min g
      exact ⟨g i, hg i, hi⟩
  obtain ⟨c, hc, hcle⟩ := hlow (ι := Σ σ : k →+* ℂ, {x // x ∈ t σ}) (fun z => ρ z.1 z.2.1) (fun z => hρ _ _)
  refine ⟨c, hc, fun N f R hf hR => ⟨hf, fun σ y => ?_⟩⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht σ (Set.mem_univ y))
  exact H σ x N f R hf (fun σ' y' h => hR σ' y' ((hcle ⟨σ, ⟨x, hx⟩⟩).trans h)) y hy

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsymptoticRiemannRochAmpleCoherentStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.asymptotic_riemannRoch_ample_coherent : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, IsAmpleLB L → ∃ C m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → |(d.factorial : ℤ) * (hdim k (twist F (lbPow L m)) 0 : ℤ) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  first | exact @GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB | exact GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB | (intros; apply GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtAlgebraMapSgnAdSubOne
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLift

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Classical

section SignAdele

variable {F : Type} [Field F] [NumberField F]

def sgnAd (w : InfinitePlace F) : AF F :=
  (((fun v : InfinitePlace F => (if v = w then -1 else 1 : v.Completion)) : Ainf F), (1 : Af F))

theorem sgnAd_mul_self (w : InfinitePlace F) : sgnAd w * sgnAd w = 1 := by
  refine Prod.ext (funext fun v => ?_) (mul_one _)
  show (if v = w then -1 else 1 : v.Completion) * (if v = w then -1 else 1) = 1
  split_ifs <;> simp

theorem evInf_sgnAd (w v : InfinitePlace F) : evInf F v (sgnAd w) = if v = w then -1 else 1 := rfl

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem piInf_algebraMap {v : InfinitePlace F} (τ : EmbOver E v) (y : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) y) = InfinitePlace.Completion.extensionEmbedding v (evInf F v y) := by
  unfold piInf
  rw [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply]
  simp [compInf]

theorem at_algebraMap_sgnAd_sub_one (w : InfinitePlace F) :
    At (evI F) (algebraMap (AF F) (AE F E) (sgnAd w) - 1) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  have h2 : u * (sgnAd w - 1) = 0 := by
    refine Prod.ext ?_ ?_
    · show u.1 * _ = 0
      rw [h1, zero_mul]
    · show u.2 * ((1 : Af F) - 1) = 0
      rw [sub_self, mul_zero]
  rw [← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul, h2, map_zero]

end SignAdele

theorem even_im_hermitian_sub : Parity := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT w
  let u : (AF F)ˣ := ⟨sgnAd w, sgnAd w, sgnAd_mul_self w, sgnAd_mul_self w⟩
  let z : (AE F E)ˣ := Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) u
  have hz : At (evI F) ((z : AE F E) - 1) := at_algebraMap_sgnAd_sub_one w
  have hpi : ∀ v, piInf (B.emb v) (z : AE F E) = if v = w then -1 else 1 := by
    intro v
    show piInf (B.emb v) (algebraMap (AF F) (AE F E) (sgnAd w)) = _
    rw [piInf_algebraMap, evInf_sgnAd]
    split_ifs <;> simp
  have hexp : ∀ m : InfinitePlace F → ℤ,
      ∏ v, (piInf (B.emb v) (z : AE F E) / ‖piInf (B.emb v) (z : AE F E)‖) ^ m v = (-1 : ℂ) ^ m w := by
    intro m
    rw [Finset.prod_eq_single w (fun v _ hv => by rw [hpi, if_neg hv]; simp) (fun h => absurd (Finset.mem_univ w) h),
      hpi, if_pos rfl]
    simp
  have eα := hT.chars.expα z hz
  have eβ := hT.chars.expβ z hz
  rw [hexp] at eα eβ
  have rα : (X.α z : ℂ) = _ := hT.chars.resα u
  have rβ : (X.β z : ℂ) = _ := hT.chars.resβ u
  have hpar : ((-1 : ℂ)) ^ a' = (-1) ^ a := by
    have he := hT.geo.even
    rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, ((Nat.even_add.1 he).1 ha).neg_one_pow]
    · have ha' : Odd a' := Nat.not_even_iff_odd.1 fun h => Nat.not_even_iff_odd.2 ha ((Nat.even_add.1 he).2 h)
      rw [ha.neg_one_pow, ha'.neg_one_pow]
  have hab : (-1 : ℂ) ^ B.mα w = (-1) ^ B.mβ w := by
    rw [← eα, ← eβ, rα, rβ, hpar]
  rcases Int.even_or_odd (B.mα w - B.mβ w) with h | h
  · exact h
  · exfalso
    have h1 := h.neg_one_zpow (α := ℂ)
    rw [zpow_sub₀ (by norm_num), hab, div_self (zpow_ne_zero _ (by norm_num))] at h1
    norm_num at h1
end GlobalTheory.RealLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLift.HermitianFrameExistence

open Matrix
open scoped ComplexOrder

theorem map_star_trip {m k l o : Type} [Fintype k] [Fintype l] (X : Matrix k m ℂ) (Y : Matrix k l ℂ)
    (Z : Matrix l o ℂ) : (Xᵀ * Y * Z.map star).map star = Xᴴ * Y.map star * Z := by
  have h : ∀ {a b : Type} (W : Matrix a b ℂ), W.map star = W.map (starRingEnd ℂ) := fun _ => rfl
  rw [h (Xᵀ * Y * Z.map star), Matrix.map_mul, Matrix.map_mul]
  simp [Matrix.conjTranspose, Matrix.map_map, Function.comp_def]

theorem quad {n ι : Type} [Fintype n] [Fintype ι] (G : Matrix n n ℂ) (B : Matrix n ι ℂ) (w : ι → ℂ) :
    star (B *ᵥ w) ⬝ᵥ G *ᵥ (B *ᵥ w) = star w ⬝ᵥ (Bᴴ * G * B) *ᵥ w := by
  conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

theorem val_inl {p q : ℕ} (u : Fin p → ℂ) :
    star (Sum.elim u (0 : Fin q → ℂ)) ⬝ᵥ (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      Sum.elim u 0 = star u ⬝ᵥ u := by
  simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]

theorem val_inr {p q : ℕ} (v : Fin q → ℂ) :
    star (Sum.elim (0 : Fin p → ℂ) v) ⬝ᵥ (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      Sum.elim 0 v = -(star v ⬝ᵥ v) := by
  simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, neg_mulVec, Finset.sum_neg_distrib]

theorem inertia {n p q r s : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
    (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ) (hB : Bᴴ * G * B = fromBlocks 1 0 0 (-1))
    (hA : Aᴴ * G * A = fromBlocks 1 0 0 (-1)) : p + s ≤ n := by
  have key : ∀ (u : Fin p → ℂ) (v : Fin s → ℂ), B *ᵥ Sum.elim u 0 = A *ᵥ Sum.elim 0 v → u = 0 ∧ v = 0 := by
    intro u v h
    have h1 := quad G B (Sum.elim u 0)
    have h2 := quad G A (Sum.elim 0 v)
    rw [hB, val_inl] at h1
    rw [hA, val_inr, ← h, h1] at h2
    have hu := dotProduct_star_self_nonneg u
    have hv := dotProduct_star_self_nonneg v
    have h3 : star u ⬝ᵥ u = 0 := le_antisymm (by rw [h2]; exact neg_nonpos.2 hv) hu
    have h4 : star v ⬝ᵥ v = 0 := by rw [h3] at h2; exact neg_eq_zero.1 h2.symm
    exact ⟨dotProduct_star_self_eq_zero.1 h3, dotProduct_star_self_eq_zero.1 h4⟩
  let f : (Fin p → ℂ) × (Fin s → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    B.mulVecLin ∘ₗ ((LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℂ ℂ).symm.toLinearMap ∘ₗ
        (LinearMap.inl ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _)) -
      A.mulVecLin ∘ₗ ((LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm.toLinearMap ∘ₗ
        (LinearMap.inr ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _))
  have e1 : ∀ u : Fin p → ℂ, (LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℂ ℂ).symm (u, 0) = Sum.elim u 0 := by
    intro u; ext (i | i) <;> simp
  have e2 : ∀ v : Fin s → ℂ, (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm ((0 : Fin r → ℂ), v) = Sum.elim (0 : Fin r → ℂ) v := by
    intro v; ext (i | i) <;> simp
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, v⟩ huv
    have h0 : B *ᵥ Sum.elim u 0 - A *ᵥ Sum.elim 0 v = 0 := by
      simpa [f, e1, e2, Matrix.mulVecLin_apply] using huv
    obtain ⟨hu, hv⟩ := key u v (sub_eq_zero.1 h0)
    simp [hu, hv]
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_prod] using this

theorem card_le_of_mul_eq_one {m k : Type} [Fintype m] [Fintype k] [DecidableEq m] (X : Matrix m k ℂ)
    (Y : Matrix k m ℂ) (h : X * Y = 1) : Fintype.card m ≤ Fintype.card k := by
  have hi : Function.Injective Y.mulVecLin := by
    intro u v huv
    have := congrArg (fun w => X *ᵥ w) huv
    simpa [Matrix.mulVecLin_apply, mulVec_mulVec, h] using this
  simpa using LinearMap.finrank_le_finrank_of_injective hi

theorem star_form {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v y : Fin n → ℂ) :
    star (v ⬝ᵥ M *ᵥ star y) = star v ⬝ᵥ M.map star *ᵥ y := by
  simp [dotProduct, mulVec, star_sum, Finset.mul_sum, mul_comm, mul_left_comm]

end GlobalTheory.RealLift.HermitianFrameExistence

namespace GlobalTheory.RealLift

open Matrix GlobalTheory.RealLift.HermitianFrameExistence
open scoped ComplexOrder

theorem frameEx_holds : FrameEx := by
  intro n r s M θ hSig hC
  obtain ⟨hrs, A0, hA0⟩ := hSig
  obtain ⟨hθθ, hiso, hpos⟩ := hC
  set G : Matrix (Fin n) (Fin n) ℂ := M.map star with hGdef
  have hJ : ∀ p q : ℕ, (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map star =
      fromBlocks 1 0 0 (-1) := by
    intro p q; ext (i | i) (j | j) <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
  have hA : A0ᴴ * G * A0 = fromBlocks 1 0 0 (-1) := by
    rw [← map_star_trip, hA0, hJ]

  obtain ⟨L, hLdef⟩ : ∃ L : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ,
      L = (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * (A0ᴴ * G) := ⟨_, rfl⟩
  have hL : L * A0 = 1 := by
    calc L * A0 = (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * (A0ᴴ * G * A0) := by
          rw [hLdef]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, fromBlocks_multiply]; simp
  have e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hR : A0 * L = 1 := (mul_eq_one_comm_of_equiv e).1 hL
  have hLc : Lᴴ * A0ᴴ = 1 := by rw [← conjTranspose_mul, hR, conjTranspose_one]
  have hJh : ((fromBlocks 1 0 0 (-1)) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)ᴴ = fromBlocks 1 0 0 (-1) := by
    simp [fromBlocks_conjTranspose]
  have hA' : A0ᴴ * Gᴴ * A0 = A0ᴴ * G * A0 := by
    calc A0ᴴ * Gᴴ * A0 = (A0ᴴ * G * A0)ᴴ := by simp [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hA, hJh]
  have Gherm : Gᴴ = G := by
    calc Gᴴ = (Lᴴ * A0ᴴ) * Gᴴ * (A0 * L) := by rw [hLc, hR]; simp
      _ = Lᴴ * (A0ᴴ * Gᴴ * A0) * L := by simp only [Matrix.mul_assoc]
      _ = Lᴴ * (A0ᴴ * G * A0) * L := by rw [hA']
      _ = (Lᴴ * A0ᴴ) * G * (A0 * L) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hLc, hR]; simp

  have hiso' : θᴴ * G * θ = G := by rw [← map_star_trip, hiso]
  have hcomm : θᴴ * G = G * θ := by
    calc θᴴ * G = θᴴ * G * θ * θ := by rw [Matrix.mul_assoc (θᴴ * G), hθθ, Matrix.mul_one]
      _ = G * θ := by rw [hiso']
  have hherm : (G * θ).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, Gherm, hcomm]
  have hPD : (G * θ).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hherm, fun x hx => ?_⟩
    have hval : star x ⬝ᵥ (G * θ) *ᵥ x = star ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
      rw [← hcomm, star_form, ← hGdef, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    refine Complex.pos_iff.2 ⟨?_, (hherm.im_star_dotProduct_mulVec_self x).symm⟩
    rw [hval, Complex.star_def, Complex.conj_re]; exact hpos x hx
  obtain ⟨p, q, B, B', h1, h2, h3, h4⟩ :=
    GlobalTheory.exists_basis_adapted_to_cartan_involution n G θ hθθ hiso' hPD
  have i1 := inertia G B A0 h3 hA
  have i2 := inertia G A0 B hA h3
  have i3 := card_le_of_mul_eq_one B B' h1
  simp only [Fintype.card_fin, Fintype.card_sum] at i3
  obtain rfl : p = r := by omega
  obtain rfl : q = s := by omega
  refine ⟨B, ⟨?_, B', h1⟩, h4⟩
  calc Bᵀ * M * B.map star = ((Bᵀ * M * B.map star).map star).map star := by simp [Matrix.map_map, Function.comp_def]
    _ = _ := by rw [map_star_trip, ← hGdef, h3, hJ]; rfl

end GlobalTheory.RealLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirGlFactorEmbeddingMemCapelliAlgebra
section
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CasCentre

open Finset Polynomial

variable {A : Type} [Ring A] [Algebra ℂ A]

def pS {n : ℕ} (s : Finset (Fin n)) : ℂ[X] := ∏ l ∈ s, (X - C ((l : ℕ) : ℂ))

theorem natDegree_pS {n : ℕ} (s : Finset (Fin n)) : (pS s).natDegree = s.card :=
  natDegree_finsetProd_X_sub_C_eq_card _ _

theorem prod_eq_sum {n : ℕ} (s : Finset (Fin n)) (u : ℂ) :
    ∏ l ∈ s, (u - (l : ℂ)) = ∑ k ∈ range (n + 1), u ^ k * (pS s).coeff k := by
  have h1 : (pS s).eval u = ∏ l ∈ s, (u - (l : ℂ)) := by simp [pS, eval_prod]
  have h2 : (pS s).natDegree < n + 1 := by
    rw [natDegree_pS]; have := Finset.card_le_univ s; simp at this; omega
  rw [← h1, eval_eq_sum_range' h2]
  exact sum_congr rfl fun k _ => mul_comm _ _

theorem coeff_pS_top {n : ℕ} (s : Finset (Fin n)) : (pS s).coeff s.card = 1 := by
  have hm : (pS s).Monic := monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  rw [← natDegree_pS]; exact hm.coeff_natDegree

theorem coeff_pS_next {n : ℕ} (s : Finset (Fin n)) (hs : 0 < s.card) :
    (pS s).coeff (s.card - 1) = -∑ l ∈ s, (l : ℂ) := by
  have h := prod_X_sub_C_nextCoeff (s := s) (fun l : Fin n => ((l : ℕ) : ℂ))
  rw [nextCoeff_of_natDegree_pos (by rw [natDegree_finsetProd_X_sub_C_eq_card]; exact hs),
    natDegree_finsetProd_X_sub_C_eq_card] at h
  exact h

theorem sum_fin_cast (n : ℕ) : 2 * ∑ l : Fin n, (l : ℂ) = (n : ℂ) * ((n : ℂ) - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Finset.sum_range_id_mul_two n
  rw [Fin.sum_univ_eq_sum_range (fun l => ((l : ℕ) : ℂ)) n]
  have h' : ((∑ i ∈ range n, i : ℕ) : ℂ) * 2 = ((n * (n - 1) : ℕ) : ℂ) := by exact_mod_cast h
  rw [Nat.cast_mul, Nat.cast_sub (by omega)] at h'
  push_cast at h'
  linear_combination h'

theorem cas_mem_of_qdet_mem {n : ℕ} (X : Fin n → Fin n → A) (hX : Formalism.REAL.GlRel X) (S : Subalgebra ℂ A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet X u ∈ S) : Formalism.REAL.Cas X ∈ S := by
  classical
  have hT : ∑ i, X i i ∈ S := GlobalTheory.CapTrace.trace_mem_of_qdet_mem X S h
  rcases lt_or_ge n 2 with hn | hn
  · have e : Formalism.REAL.Cas X = (∑ i, X i i) * (∑ i, X i i) := by
      interval_cases n <;> simp [Formalism.REAL.Cas]
    rw [e]; exact S.mul_mem hT hT
  obtain ⟨Rm, hR⟩ := GlobalTheory.qdet_top_three_orders A n X
  let Cf : ℕ → A := fun k => (pS (univ : Finset (Fin n))).coeff k • (1 : A) +
    ∑ i, (pS (univ.erase i)).coeff k • X i i +
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (pS ((univ.erase i).erase j)).coeff k • (X i i * X j j - X j i * X i j) +
    (if k < n - 2 then Rm k else 0)
  have hexp : ∀ u : ℂ, Formalism.REAL.qdet X u = ∑ k ∈ range (n + 1), u ^ k • Cf k := by
    intro u
    have hRm : ∑ k ∈ range (n + 1), u ^ k • (if k < n - 2 then Rm k else 0) = ∑ d ∈ range (n - 2), u ^ d • Rm d := by
      simp only [smul_ite, smul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext k; simp only [mem_filter, mem_range]; omega
    rw [hR u]
    simp only [Cf, smul_add, sum_add_distrib, hRm, prod_eq_sum, sum_smul, smul_sum, smul_smul]
    congr 1
    congr 1
    · congr 1
      exact sum_comm
    · rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      exact sum_comm
  have hmem : Cf (n - 2) ∈ S :=
    GlobalTheory.CapTrace.coeff_mem (Subalgebra.toSubmodule S) n Cf (fun u => by rw [← hexp]; exact h u) (n - 2) (by omega)
  have hc2 : ∀ i : Fin n, ∀ j ∈ univ.filter (fun j => i < j), (pS ((univ.erase i).erase j)).coeff (n - 2) = 1 := by
    intro i j hj
    have hij : j ≠ i := (mem_filter.1 hj).2.ne'
    have hc : ((univ.erase i).erase j).card = n - 2 := by
      rw [card_erase_of_mem (mem_erase.2 ⟨hij, mem_univ _⟩), card_erase_of_mem (mem_univ _), card_univ,
        Fintype.card_fin]; omega
    rw [← hc]; exact coeff_pS_top _
  have hc1 : ∀ i : Fin n, (pS (univ.erase i)).coeff (n - 2) = -∑ l ∈ univ.erase i, (l : ℂ) := by
    intro i
    have hc : (univ.erase i).card = n - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have := coeff_pS_next (univ.erase i) (by omega)
    rw [hc, show n - 1 - 1 = n - 2 by omega] at this
    exact this
  set c := (pS (univ : Finset (Fin n))).coeff (n - 2)
  have hC : Cf (n - 2) = c • (1 : A) + ∑ i, (pS (univ.erase i)).coeff (n - 2) • X i i +
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (X i i * X j j - X j i * X i j) := by
    simp only [Cf, lt_irrefl, if_false, add_zero]
    congr 1
    exact sum_congr rfl fun i _ => sum_congr rfl fun j hj => by rw [hc2 i j hj, one_smul]
  have h3 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • X i i + (2 : ℂ) • ∑ i, (pS (univ.erase i)).coeff (n - 2) • X i i
      = -(((n : ℂ) - 1) ^ 2) • ∑ i, X i i := by
    rw [smul_sum, smul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← add_smul, hc1, sum_erase_eq_sub (mem_univ _)]
    congr 1
    have := sum_fin_cast n
    linear_combination (-1 : ℂ) * this
  have h1 := GlobalTheory.CapelliCasimir.sq_sub_cas X hX
  have key : Formalism.REAL.Cas X = (∑ i, X i i) * (∑ i, X i i) - (2 : ℂ) • Cf (n - 2) + (2 * c) • (1 : A)
      - (((n : ℂ) - 1) ^ 2) • ∑ i, X i i := by
    linear_combination (norm := module) (-1 : ℂ) • h1 + (2 : ℂ) • hC + h3
  rw [key]
  exact S.sub_mem (S.add_mem (S.sub_mem (S.mul_mem hT hT) (S.smul_mem hmem _)) (S.smul_mem (S.one_mem) _))
    (S.smul_mem hT _)

theorem cas_Eop_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  intro E _ _ _ a τ
  refine cas_mem_of_qdet_mem (Eop τ) (glRel_Eop τ) (Zalg E a) fun u => ?_
  have e : Formalism.REAL.qdet (Eop (a := a) τ) u = cap τ (u - ((a : ℂ) - 1) / 2) := by
    rw [cap]; congr 1; ring
  rw [e]
  exact Algebra.subset_adjoin ⟨τ, _, rfl⟩

end GlobalTheory.CasCentre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnity
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.NuGood

theorem not_root_of_unity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h v hv t k hk hpow
  have hW : splitPrime t ∉ above E (X.T : Set (Pl (F := F))) := by
    intro hmem
    exact hv.1 (by simpa [above, splitPrime_under] using hmem)
  have hunr : UnrAt X.ν (splitPrime t) := by
    rw [Chars.ν, div_eq_mul_inv]
    exact (h.chars.unrα _ hW).mul (h.chars.unrβ _ hW).inv
  rw [GlobalTheory.T.unramified_character_at_uniformizer F E X.ν v t hunr] at hpow
  have hHecke : IsHecke F E X.ν := by
    refine ⟨?_, fun x => ?_⟩
    · exact (h.chars.heckeα.1.div' h.chars.heckeβ.1 :)
    · rw [Chars.ν, MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_one]
  obtain ⟨H, hloc, hinf⟩ := _root_.GlobalTheory.HeckeBridge.exists_hchar F E σ h.base.cm X.ν hHecke
  have hexp : HasExp B.emb X.ν (fun w => B.mα w - B.mβ w) := by
    intro z hz
    have h1 := h.chars.expα z hz
    have h2 := h.chars.expβ z hz
    show (((X.α z / X.β z : Circle)) : ℂ) = _
    rw [Circle.coe_div, h1, h2, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hne : piInf (B.emb w) z ≠ 0 := (z.isUnit.map (piInf (B.emb w))).ne_zero
    have hne' : piInf (B.emb w) z / (‖piInf (B.emb w) z‖ : ℂ) ≠ 0 :=
      div_ne_zero hne (by exact_mod_cast (norm_ne_zero_iff.2 hne))
    rw [zpow_sub₀ hne']
  have hval : val X.ν (splitPrime t) = H.val (splitPrime t) := (hloc _ _).symm
  obtain ⟨p, hp, hN, hsq⟩ := GlobalTheory.T.split_prime_degree_one F E (splitPrime t) (by rw [splitPrime_under]; exact hv.2)
  refine _root_.GlobalTheory.CMSplitValue.not_isOfFinOrder_val F E σ h.base.cm h.base.galois B.emb H _ (hinf _ _ hexp) (fun w => ?_) p hp _ hN hsq ?_
  · have := h.geo.kappa w
    omega
  · rw [← hval]
    exact isOfFinOrder_iff_zpow_eq_one.2 ⟨k, hk, hpow⟩

end GlobalTheory.NuGood
end

