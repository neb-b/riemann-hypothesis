module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0217
public import ReciprocityTheory.NeutralLocalFields.Bundle0001
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipB
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicJetsOfAlgebraicTaylor
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.AlgJetsRat

variable {D : D7} {N N' : ℕ}

theorem jet_embV_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (F : VC D N N' → ℂ) (hF : ContDiff ℂ ⊤ F)
    (hT : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D F α ∈ Qbar) {m : ℕ} (A : Fin m → Matrix (Fin N') (Fin N) D.host.E) :
    iteratedFDeriv ℂ m F 0 (fun j => embV D (tor0 D cc δ) (A j)) ∈ Qbar := by
  rw [GlobalTheory.JetTransport.mlin_expand]
  refine IntermediateField.sum_mem _ fun f _ => IntermediateField.mul_mem _ ?_ ?_
  · exact IntermediateField.prod_mem _ fun j _ => GlobalTheory.JetTransport.embT_mem _ _
  · rw [GlobalTheory.JetTransport.iFD_coord F hF f]
    refine IntermediateField.mul_mem _ (IntermediateField.prod_mem _ fun i _ => ?_) (hT _)
    exact IntermediateField.natCast_mem _ _

end GlobalTheory.AlgJetsRat

open GlobalTheory.AlgJetsRat in
theorem GlobalTheory.algJets_of_taylor : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (F : VC D N N' → ℂ), δ / δ₀ ∈ Qbar → δ₀ ≠ 0 → ContDiff ℂ ⊤ F → (∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D F α ∈ Qbar) → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') → S.AlgJets δ₀ (fun z => F (e.symm z)) := by
  intro D cc δ δ₀ B N N' L L' F hδ hδ₀ hF hT g S e he hLa k ys hys
  have hc : ∀ j, ∃ (c : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E),
      c ∈ Qbar ∧ e.symm (δ₀⁻¹ • ys j) = c • embV D B.tor A := by
    intro j
    obtain ⟨s, hs, hsy⟩ := hys j
    have hx : e.symm ((s : ℂ) • ys j) ∈ La D B.tor L L' := (he _).1 (by simpa using hsy)
    obtain ⟨n, A, -, hA, -⟩ := hLa _ hx
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    refine ⟨δ / δ₀ * (s : ℂ)⁻¹, A, IntermediateField.mul_mem _ hδ
      (IntermediateField.inv_mem _ (IntermediateField.natCast_mem _ s)), ?_⟩
    have h1 : e.symm (ys j) = (s : ℂ)⁻¹ • (δ • embV D B.tor A) := by
      rw [← hA, map_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [map_smul, h1, smul_smul, smul_smul]
    congr 1
    field_simp
  choose c A hcQ hcA using hc
  show iteratedFDeriv ℂ k (F ∘ ((e.symm : (Fin g → ℂ) ≃L[ℂ] VC D N N') : (Fin g → ℂ) →L[ℂ] VC D N N')) 0
    (fun j => δ₀⁻¹ • ys j) ∈ Qbar
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hF _ le_top,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearEquiv.coe_coe, map_zero, hcA]
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  exact IntermediateField.mul_mem _ (IntermediateField.prod_mem _ fun j _ => hcQ j)
    (jet_embV_mem cc δ F hF hT A)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomDict

open GlobalTheory.MomOne

theorem root_eq (d : ℕ) (hd : d % 4 = 3) (t n : ℤ) (hD : t ^ 2 - 4 * n = -(d : ℤ)) (β : ℂ)
    (hβ : β ^ 2 = t * β - n) : ∃ k : ℤ, β = k + wK d ∨ β = k - wK d := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, t = 2 * k + 1 := by
    rcases Int.even_or_odd' t with ⟨k, rfl | rfl⟩
    · exfalso
      have : (2 * k) ^ 2 = 4 * (k * k) := by ring
      rw [this] at hD
      generalize k * k = m at hD
      omega
    · exact ⟨k, rfl⟩
  obtain ⟨s, hs2, hw⟩ : ∃ s : ℂ, s ^ 2 = -(d : ℂ) ∧ wK d = (1 + s) / 2 := by
    refine ⟨Complex.I * ((Real.sqrt d : ℝ) : ℂ), ?_, rfl⟩
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast; ring
  have hDc : (t : ℂ) ^ 2 - 4 * n = -(d : ℂ) := by exact_mod_cast hD
  have hprod : (2 * β - t - s) * (2 * β - t + s) = 0 := by
    linear_combination 4 * hβ + hDc - hs2
  have hkc : (t : ℂ) = 2 * k + 1 := by exact_mod_cast hk
  rcases mul_eq_zero.1 hprod with h | h
  · refine ⟨k, Or.inl ?_⟩
    rw [hw]; linear_combination h / 2 + hkc / 2
  · refine ⟨k + 1, Or.inr ?_⟩
    rw [hw]; push_cast; linear_combination h / 2 + hkc / 2

theorem inOK_iff_int_pair (d : ℕ) (β : ℂ) (k : ℤ) (hβ : β = k + wK d ∨ β = k - wK d) (z : ℂ) :
    InOK d z ↔ ∃ x y : ℤ, z = x + y * β := by
  rcases hβ with rfl | rfl
  · constructor
    · rintro ⟨u, v, rfl⟩; exact ⟨u - v * k, v, by push_cast; ring⟩
    · rintro ⟨x, y, rfl⟩; exact ⟨x + y * k, y, by push_cast; ring⟩
  · constructor
    · rintro ⟨u, v, rfl⟩; exact ⟨u + v * k, -v, by push_cast; ring⟩
    · rintro ⟨x, y, rfl⟩; exact ⟨x + y * k, -y, by push_cast; ring⟩

theorem inOK_iff (D : D7) (z : ℂ) :
    InOK D.host.d z ↔ ∃ x : 𝓞 D.host.K, z = D.host.φ₀ ((x : D.host.K) : D.host.E) := by
  obtain ⟨b, t, n, h0, hw, hdisc⟩ := GlobalTheory.QuadraticZeta.exists_basis (K := D.host.K) (GlobalTheory.CurveLattice.finrank_hostK D)
  rw [GlobalTheory.CurveLattice.discr_hostK D] at hdisc
  let σ : 𝓞 D.host.K →+* ℂ := D.host.φ₀.comp ((algebraMap D.host.K D.host.E).comp (algebraMap (𝓞 D.host.K) D.host.K))
  have hσ : ∀ x : 𝓞 D.host.K, σ x = D.host.φ₀ ((x : D.host.K) : D.host.E) := fun x => rfl
  have hβ : σ (b 1) ^ 2 = t * σ (b 1) - n := by
    rw [← map_pow, hw]; simp
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨k, hk⟩ := root_eq D.host.d hd4 t n hdisc.symm _ hβ
  rw [inOK_iff_int_pair D.host.d _ k hk z]
  constructor
  · rintro ⟨x, y, rfl⟩
    exact ⟨x + y * b 1, by rw [← hσ]; simp⟩
  · rintro ⟨x, rfl⟩
    refine ⟨b.repr x 0, b.repr x 1, ?_⟩
    rw [← hσ]
    conv_lhs => rw [GlobalTheory.QuadraticZeta.eq_coord b h0 x]
    simp

end GlobalTheory.MomDict

namespace GlobalTheory.MomDict

theorem area_bot : area (⊥ : AddSubgroup ℂ) = 0 := by
  unfold area
  have : {a : ℝ | 0 < a ∧ ∃ w₁ ∈ (⊥ : AddSubgroup ℂ), ∃ w₂ ∈ (⊥ : AddSubgroup ℂ), a = |((starRingEnd ℂ) w₁ * w₂).im|} = ∅ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ha ⟨w₁, h1, w₂, h2, rfl⟩
    rw [AddSubgroup.mem_bot] at h1 h2
    simp [h1, h2] at ha
  rw [this, Real.sInf_empty]

theorem lamOf_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) : lamOf D cc 0 = ⊥ := by
  ext w
  rw [GlobalTheory.CurveLattice.mem_lamOf, AddSubgroup.mem_bot]
  constructor
  · rintro ⟨c, -, rfl⟩; simp
  · rintro rfl; exact ⟨0, cc.zero_mem, by simp⟩

theorem area_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : cc ≠ ⊥) :
    area (lamOf D cc δ) = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 := by
  rcases eq_or_ne δ 0 with rfl | hδ
  · rw [lamOf_zero, area_bot]; simp
  obtain ⟨a, τ, ha, hN, h⟩ := GlobalTheory.CurveLattice.exists_tau D cc hcc
  have hda : δ * a ≠ 0 := mul_ne_zero hδ ha
  have hd : 0 < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  rw [GlobalTheory.CurveLattice.area_of_tau hda (h δ), hN, norm_mul, Complex.normSq_eq_norm_sq]
  field_simp

theorem main : ∀ (D : D7), D.host.d.Prime ∧ D.host.d % 16 = 7 ∧ (∀ z : ℂ, GlobalTheory.MomOne.InOK D.host.d z ↔ ∃ x : 𝓞 D.host.K, z = D.host.φ₀ ((x : D.host.K) : D.host.E)) ∧ (∀ x : D.host.K, D.host.φ₀ (D.host.conj (x : D.host.E)) = (starRingEnd ℂ) (D.host.φ₀ (x : D.host.E))) ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → area (lamOf D cc δ) = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ ∀ z : ℂ, z ∈ lamOf D cc δ ↔ ∃ x ∈ cc, z = δ * D.host.φ₀ ((x : D.host.K) : D.host.E) := by
  intro D
  refine ⟨D.host.hyp.2.1, D.host.hyp.2.2.2.1, inOK_iff D, fun x => D.host.conjE_apply _ _, fun cc δ hcc => ⟨area_lamOf D cc δ hcc, fun z => GlobalTheory.CurveLattice.mem_lamOf D cc δ z⟩⟩

end GlobalTheory.MomDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ColumnWeightTwisted
section
open Formalism.BasicNotions GlobalTheory.LvT

namespace GlobalTheory.Proof.ColumnWeightTwisted

theorem exists_int_m_mul_EatT (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ k : ℤ, (D.R.m : ℝ) * EatT D u w = (k : ℝ) := by
  unfold EatT
  split_ifs
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := D.R.t_odd
    refine ⟨(D.R.m : ℤ) * (2 * (∑ τ : D.what₂.Tau, (Wtau D u τ : ℤ)) + (D.R.f : ℤ) * (D.R.N D.R.m : ℤ)) +
      ((topsOf D.host D.eTau).card : ℤ) * ((b : ℤ) + 1) * ((D.R.m : ℤ) + 1) * a, ?_⟩
    have ha' : (D.R.m : ℝ) = a + a := by exact_mod_cast ha
    have hb' : (D.R.t : ℝ) = 2 * b + 1 := by exact_mod_cast hb
    unfold Formalism.MainNotions.G.Nm
    push_cast
    rw [hb', ha']
    ring
  · exact ⟨0, by simp⟩

theorem colGeTw_of_tupleChainSharpColumnValuation : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup), TupleChainSharpColumnValuation T u μ → ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T → ∀ x ∈ LT.Nlam D u w, Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w)) := by
  intro D T u μ h w hw x hx
  obtain ⟨k, hk⟩ := exists_int_m_mul_EatT D u w
  obtain ⟨c, hc⟩ := D.what₂.places.val_surj w ((D.what₂.places.ramIdx w : ℤ) * k)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hc
    exact WithTop.top_ne_coe hc
  obtain ⟨y, hy, e⟩ := h w hw c _ hc (by rw [hk]; push_cast; exact le_rfl) x hx
  have hv : vAdd (D.plEq w) c = (D.what₂.places.ramIdx w : ℤ) * k := by
    rw [D.val_eq w _ hc0] at hc
    exact_mod_cast hc
  have hvi : vAdd (D.plEq w) c⁻¹ = - vAdd (D.plEq w) c := by
    unfold vAdd
    rw [map_inv₀, WithZero.log_inv]
  refine ⟨c⁻¹ • y, ?_, c⁻¹, y, hy, rfl, Or.inr ?_⟩
  · rw [LinearMap.map_smulₛₗ, e, smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
  · rw [hvi, hv, hk]
    unfold DV.ur
    push_cast
    exact le_of_eq (by ring)

end GlobalTheory.Proof.ColumnWeightTwisted
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EquivariantMapEqSmul
section
open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.Branching

theorem equivariant_map_eq_smul : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Formalism.MainNotions.PrimeDegreeVariant.Interlace h lam sg → ∀ (φ φ' : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), (∀ ψ, ψ = φ ∨ ψ = φ' → (∀ f ∈ nablaSq ℂ N lam, ψ f ∈ nablaSq ℂ n sg) ∧ ∀ (g : GL (Fin n) ℂ), ∀ f ∈ nablaSq ℂ N lam, ψ (sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N h g) f) = sqAct ℂ n sg g (ψ f)) → (∃ f ∈ nablaSq ℂ N lam, φ' f ≠ 0) → ∃ c : ℂ, ∀ f ∈ nablaSq ℂ N lam, φ f = c • φ' f := by
  intro n N h lam sg hI φ φ' H hne
  let mk : ∀ ψ, (ψ = φ ∨ ψ = φ') → (resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
      (smallRep (MonoidHom.id (GL (Fin n) ℂ)) sg) := fun ψ hψ =>
    ⟨ψ.restrict (H ψ hψ).1, fun g => LinearMap.ext fun f => Subtype.ext ((H ψ hψ).2 g f.1 f.2)⟩
  have h1 := (comult_id n N h lam sg).1 hI
  have hz : mk φ' (Or.inr rfl) ≠ 0 := by
    obtain ⟨f, hf, hf0⟩ := hne
    intro e
    apply hf0
    have := congrArg (fun F => ((F.toLinearMap ⟨f, hf⟩ : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ)) e
    exact this
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hz).1 h1 (mk φ (Or.inl rfl))
  refine ⟨c, fun f hf => ?_⟩
  have := congrArg (fun F => ((F.toLinearMap ⟨f, hf⟩ : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ)) hc
  exact this.symm

end GlobalTheory.Branching
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDiagMulRayMulUnif
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.RayGen

variable {K : Type} [Field K] [NumberField K]

def compAt (v : HeightOneSpectrum (𝓞 K)) : Ideles K →* v.adicCompletion K where
  toFun a := (a : AdeleRing (𝓞 K) K).2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def compInf (w : InfinitePlace K) : Ideles K →* w.Completion where
  toFun a := (a : AdeleRing (𝓞 K) K).1 w
  map_one' := rfl
  map_mul' _ _ := rfl

def unifAway (𝔮 : Ideal (𝓞 K)) : Subgroup (Ideles K) :=
  Subgroup.closure {x : Ideles K | ∃ (v : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ),
    ¬ v.asIdeal ∣ 𝔮 ∧ IsUniformiserAt K v (π : v.adicCompletion K) ∧ x = localIdele K v π}

theorem comp_of_mem_unifAway {𝔮 : Ideal (𝓞 K)} {b : Ideles K} (hb : b ∈ unifAway 𝔮) :
    (∀ w, compInf w b = 1) ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 → compAt v b = 1 := by
  induction hb using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, π, hv, -, rfl⟩ := hx
    exact ⟨(localIdele_isSupportedAt K v π).1,
      fun v' hv' => (localIdele_isSupportedAt K v π).2 v' (by rintro rfl; exact hv hv')⟩
  | one => exact ⟨fun w => map_one _, fun v _ => map_one _⟩
  | mul x y _ _ hx hy =>
    exact ⟨fun w => by rw [map_mul, hx.1, hy.1, one_mul], fun v hv => by rw [map_mul, hx.2 v hv, hy.2 v hv, one_mul]⟩
  | inv x _ hx => exact ⟨fun w => by rw [map_inv, hx.1, inv_one], fun v hv => by rw [map_inv, hx.2 v hv, inv_one]⟩

theorem exists_unifAway {𝔮 : Ideal (𝓞 K)} (c : Ideles K)
    (hc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 → Valued.v (compAt v c) = 1) :
    ∃ b ∈ unifAway 𝔮, ∀ v, Valued.v (compAt v b) = Valued.v (compAt v c) := by
  classical
  choose π hπ using exists_isUniformiserAt K
  have hfin := Filter.eventually_cofinite.mp (valued_comp_eventually K c)
  let S := hfin.toFinset
  have hS : ∀ v, v ∈ S ↔ Valued.v (compAt v c) ≠ 1 := fun v => hfin.mem_toFinset
  refine ⟨∏ v ∈ S, localIdele K v (π v) ^ ordAt K v c, Subgroup.prod_mem _ fun v hv => Subgroup.zpow_mem _
    (Subgroup.subset_closure (by exact ⟨v, π v, fun h => (hS v).1 hv (hc v h), hπ v, rfl⟩)) _, fun w => ?_⟩
  have h1 : ∀ v, v ≠ w → compAt w (localIdele K v (π v) ^ ordAt K v c) = 1 := fun v hv => by
    rw [map_zpow, show compAt w (localIdele K v (π v)) = 1 from (localIdele_isSupportedAt K v _).2 w hv.symm,
      one_zpow]
  rw [map_prod]
  by_cases hw : w ∈ S
  · rw [Finset.prod_eq_single_of_mem w hw fun v _ hv => h1 v hv, map_zpow,
      show compAt w (localIdele K w (π w)) = π w from localIdele_snd_self K w _, map_zpow₀,
      valued_eq_exp_of_isUniformiserAt K w _ (hπ w), ← WithZero.exp_zsmul, ordAt]
    rw [smul_neg, neg_smul, neg_neg, smul_eq_mul, mul_one]
    exact WithZero.exp_log (valued_comp_ne_zero K c w)
  · rw [Finset.prod_eq_one fun v hv => h1 v (fun e => hw (e ▸ hv)), map_one]
    exact (not_not.1 ((hS w).not.1 hw)).symm

theorem valued_lt_one_of_mem (v : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ∈ v.asIdeal) :
    Valued.v (algebraMap K (v.adicCompletion K) (x : K)) < 1 := by
  have e : algebraMap K (v.adicCompletion K) (x : K) =
      ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) := rfl
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_lt_one_iff_mem x).2 hx

theorem exists_approx {𝔮 : Ideal (𝓞 K)} (h𝔮 : 𝔮 ≠ ⊥) {x : 𝓞 K} (hx : x ∈ 𝔮) (hx0 : x ≠ 0) (a : Ideles K) :
    ∃ k : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 →
      Valued.v (compAt v ((diagUnits K k)⁻¹ * a) - 1) ≤ Valued.v (algebraMap K (v.adicCompletion K) (x : K))) ∧
      ∀ w : InfinitePlace K, w.IsReal → IsSquare (compInf w ((diagUnits K k)⁻¹ * a)) := by
  classical
  let T := (Ideal.finite_factors h𝔮).toFinset
  let t' : InfinitePlace K → ℝ := fun w =>
    if hw : w.IsReal then InfinitePlace.Completion.ringEquivRealOfIsReal hw (compInf w a) else 1
  have ht' : ∀ w, t' w ≠ 0 := fun w => by
    simp only [t']
    split_ifs with hw
    · exact (map_ne_zero _).2 (inf_comp_ne_zero K a w)
    · exact one_ne_zero
  let t : (K →+* ℝ) → ℝ := fun σ => t' (InfinitePlace.mk (Complex.ofRealHom.comp σ))
  let r : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v =>
    (algebraMap K (v.adicCompletion K) (x : K) * compAt v a)⁻¹
  let U : Set (((v : T) → v.1.adicCompletion K) × ((K →+* ℝ) → ℝ)) :=
    (⋂ v : T, {y | (y.1 v - compAt v.1 a) * r v.1 ∈ v.1.adicCompletionIntegers K}) ∩
      ⋂ σ : K →+* ℝ, {y | 0 < y.2 σ * t σ}
  have : Finite (K →+* ℝ) :=
    Finite.of_injective (fun σ : K →+* ℝ => Complex.ofRealHom.comp σ) (fun σ τ h => by
      ext y
      simpa using RingHom.congr_fun h y)
  have hU : IsOpen U := by
    refine (isOpen_iInter_of_finite fun v => ?_).inter (isOpen_iInter_of_finite fun σ => ?_)
    · have h : IsOpen (v.1.adicCompletionIntegers K : Set (v.1.adicCompletion K)) :=
        Valued.isOpen_valuationSubring _
      exact h.preimage ((((continuous_apply v).comp continuous_fst).sub continuous_const).mul continuous_const)
    · exact isOpen_lt continuous_const (((continuous_apply σ).comp continuous_snd).mul continuous_const)
  obtain ⟨k, hk1, hk2⟩ := (GlobalTheory.LocalQuad.denseRange_finite_real K T).exists_mem_open hU
    ⟨(fun v => compAt v.1 a, t), Set.mem_iInter.2 fun v => by simp,
      Set.mem_iInter.2 fun σ => mul_self_pos.2 (ht' _)⟩
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx0
  have h1 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 →
      Valued.v (algebraMap K (v.adicCompletion K) k - compAt v a) ≤
        Valued.v (algebraMap K (v.adicCompletion K) (x : K)) * Valued.v (compAt v a) := fun v hv => by
    have h : Valued.v ((algebraMap K (v.adicCompletion K) k - compAt v a) * r v) ≤ 1 :=
      Set.mem_iInter.1 hk1 ⟨v, (Ideal.finite_factors h𝔮).mem_toFinset.2 hv⟩
    have h0 : Valued.v (algebraMap K (v.adicCompletion K) (x : K) * compAt v a) ≠ 0 :=
      (map_ne_zero _).2 (mul_ne_zero ((map_ne_zero _).2 hxK) (comp_ne_zero K a v))
    rwa [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 h0), one_mul, map_mul] at h
  have h2 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔮 →
      Valued.v (algebraMap K (v.adicCompletion K) k) = Valued.v (compAt v a) := fun v hv => by
    refine Valuation.map_eq_of_sub_lt _ ((h1 v hv).trans_lt ?_)
    exact mul_lt_of_lt_one_left (zero_lt_iff.2 (valued_comp_ne_zero K a v))
      (valued_lt_one_of_mem v (Ideal.le_of_dvd hv hx))
  have h3 : ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < InfinitePlace.embedding_of_isReal hw k *
      InfinitePlace.Completion.ringEquivRealOfIsReal hw (compInf w a) := fun w hw => by
    have h : 0 < InfinitePlace.embedding_of_isReal hw k * t (InfinitePlace.embedding_of_isReal hw) :=
      Set.mem_iInter.1 hk2 _
    have e : InfinitePlace.mk (Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw)) = w := by
      refine Eq.trans ?_ (InfinitePlace.mk_embedding w)
      congr 1
      ext y
      simp
    change 0 < _ * t' _ at h
    rw [e] at h
    simpa only [t', dif_pos hw] using h
  by_cases hk : k = 0
  · subst hk
    refine ⟨1, fun v hv => absurd (h2 v hv).symm ?_, fun w hw => absurd (h3 w hw) (by simp)⟩
    rw [map_zero, map_zero]
    exact valued_comp_ne_zero K a v
  refine ⟨Units.mk0 k hk, fun v hv => ?_, fun w hw => ?_⟩
  · have hk' : algebraMap K (v.adicCompletion K) k ≠ 0 := (map_ne_zero _).2 hk
    rw [map_mul, map_inv, show compAt v (diagUnits K (Units.mk0 k hk)) = algebraMap K (v.adicCompletion K) k from rfl,
      show (algebraMap K (v.adicCompletion K) k)⁻¹ * compAt v a - 1 =
        (compAt v a - algebraMap K (v.adicCompletion K) k) * (algebraMap K (v.adicCompletion K) k)⁻¹ by
          field_simp, map_mul, map_inv₀, h2 v hv, Valuation.map_sub_swap,
      mul_inv_le_iff₀ (c := Valued.v (compAt v a)) (zero_lt_iff.2 (valued_comp_ne_zero K a v))]
    exact h1 v hv
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have he : e (algebraMap K w.Completion k) = InfinitePlace.embedding_of_isReal hw k := by
      simp [e, AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
    have hp : 0 < e (compInf w ((diagUnits K (Units.mk0 k hk))⁻¹ * a)) := by
      rw [map_mul, map_inv, show compInf w (diagUnits K (Units.mk0 k hk)) = algebraMap K w.Completion k from rfl,
        map_mul, map_inv₀, he, mul_comm, ← div_eq_mul_inv, div_pos_iff, ← mul_pos_iff, mul_comm]
      exact h3 w hw
    have := (Real.isSquare_iff.2 hp.le).map e.symm
    rwa [e.symm_apply_apply] at this

theorem exists_diag_mul_ray_mul_unif : ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → ∀ a : Ideles K, ∃ k : Kˣ, ∃ u ∈ rayUnits K 𝔮 {w | w.IsReal}, ∃ b ∈ Subgroup.closure {x : Ideles K | ∃ (v : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ), ¬ v.asIdeal ∣ 𝔮 ∧ IsUniformiserAt K v (π : v.adicCompletion K) ∧ x = localIdele K v π}, a = diagUnits K k * u * b := by
  intro K _ _ 𝔮 h𝔮 a
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔮
  obtain ⟨k, hk1, hk2⟩ := exists_approx h𝔮 hx hx0 a
  set c := (diagUnits K k)⁻¹ * a with hc
  obtain ⟨b, hb, hbv⟩ := exists_unifAway (𝔮 := 𝔮) c fun v hv => by
    rw [Valuation.map_eq_of_sub_lt _ (x := 1), map_one]
    rw [map_one]
    exact (hk1 v hv).trans_lt (valued_lt_one_of_mem v (Ideal.le_of_dvd hv hx))
  obtain ⟨hb1, hb2⟩ := comp_of_mem_unifAway hb
  refine ⟨k, c * b⁻¹, ⟨fun w hw => ?_, fun v => ?_⟩, b, hb, by rw [hc]; group⟩
  · change IsSquare (compInf w (c * b⁻¹))
    rw [map_mul, map_inv, hb1, inv_one, mul_one]
    exact hk2 w hw
  · have h1 : Valued.v (compAt v (c * b⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_inv₀, hbv]
      exact mul_inv_cancel₀ (valued_comp_ne_zero K c v)
    refine ⟨h1, ?_⟩
    change ∃ x ∈ 𝔮, Valued.v (compAt v (c * b⁻¹) - 1) ≤ _
    by_cases hv : v.asIdeal ∣ 𝔮
    · rw [map_mul, map_inv, hb2 v hv, inv_one, mul_one]
      exact ⟨x, hx, hk1 v hv⟩
    · obtain ⟨y, hy, hyv⟩ := SetLike.not_le_iff_exists.mp (Ideal.dvd_iff_le.not.1 hv)
      refine ⟨y, hy, ?_⟩
      rw [valued_algebraMap_eq_one K v y hyv]
      exact Valuation.map_sub_le _ h1.le (map_one _).le

end GlobalTheory.RayGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsGeneratorsMemCompletedLatticeIffStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generators_mem_completedLattice_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∃ (m : ℕ) (l : Fin m → Fin k → E), (∀ j, l j ∈ Λ) ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R) (u : Fin k → E ⊗[F] R), u ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S₂) Λ ↔ ∃ t : Fin m → R, (∀ j, t j ∈ S₂) ∧ u = fun i => ∑ j, l j i ⊗ₜ[F] t j := by
  first | exact @GlobalTheory.OverCompare.exists_generators_mem_latS_iff | exact GlobalTheory.OverCompare.exists_generators_mem_latS_iff | (intros; apply GlobalTheory.OverCompare.exists_generators_mem_latS_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsInertiaLift
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped nonZeroDivisors

namespace GlobalTheory.CMRam

theorem val_int_le {E Ω : Type*} [Field E] [Field Ω] (ι : E →+* Ω) (A : ValuationSubring Ω) (a : 𝓞 E) :
    A.valuation (ι a) ≤ 1 :=
  (A.valuation_le_one_iff _).2
    (ReciprocityTheory.Gal.mem_of_isIntegral_int A (a.isIntegral_coe.map ι.toIntAlgHom))

theorem exists_den_field {E Ω : Type*} [Field E] [NumberField E] [Field Ω] (ι : E →+* Ω)
    (A : ValuationSubring Ω) {x : E} (hx : A.valuation (ι x) ≤ 1) :
    ∃ s t : 𝓞 E, A.valuation (ι s) = 1 ∧ (s : E) * x = t := by
  first
  | exact @_root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator
  | exact _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator
  | (apply _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator ..)

end GlobalTheory.CMRam
end

