module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMuModelMeasureOfEigenfunctional
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralPowerSeriesBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.AvgMF
section
open UpperTheory.V.Z.Kato.Joint GlobalTheory.EisM

theorem UpperTheory.V.Z.Kato.Joint.avgMF :
    UpperTheory.V.Z.Kato.Joint.AvgMF := by
  intro k l N m θ χ f t α B c hp hk hodd hN hlN hm hχ hf hα hE
  haveI : NeZero N := ⟨hN.ne'⟩
  have hsq : ∀ ν : DirichletCharacter ℂ N, ν (-1) * ν (-1) = 1 := fun ν => by rw [← map_mul]; simp
  have hform : ∀ ν : DirichletCharacter ℂ N, ν (-1) = -θ (-1) → MF k (N * l) (ch (θ⁻¹ * ν)) (frm l N m k θ ν f) :=
    fun ν hν => (GlobalTheory.iterU_level_val_stable k N l m (θ⁻¹ * ν) (fun _ => 0) α B c _ (by omega) hp hα
      (_root_.GlobalTheory.EisM.zm_fun_mf k N l m (θ⁻¹ * ν) θ ν f hk hodd hN hp hm hlN rfl hν hf)).1
  have hsign : (θ * χ) (-1) = -θ (-1) := by
    rw [MulChar.coeToFun_mul, Pi.mul_apply, hχ]; ring
  have hmain := hform (θ * χ) hsign
  rw [inv_mul_cancel_left] at hmain
  refine ⟨hmain, ?_⟩
  have hφ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hN).ne'
  have htw : tw2 N (θ (-1)) =
      fun y => ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) * ch ν y := by
    funext y
    rw [_root_.GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum N (θ (-1)) hN y, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have hmes : mesMu k l (hat θ) (tw2 N (θ (-1))) α B c m f =
      ∑ ν : DirichletCharacter ℂ N, ((N.totient : ℂ)⁻¹ * (1 - θ (-1) * ν (-1))) *
        ((α ^ m)⁻¹ * lam B c (frm l N m k θ ν f)) := by
    unfold mesMu
    rw [htw, funext (measMu_zm_sum k l (hat θ) Finset.univ _ _ _), measMu_val_sum]
    rfl
  rw [hmes, Finset.sum_eq_single_of_mem (θ * χ) (Finset.mem_univ _)]
  · have h2 : (1 : ℂ) - θ (-1) * (θ * χ) (-1) = 2 := by
      rw [hsign]; linear_combination hsq θ
    rw [h2]
    field_simp
  · intro ν _ hne
    have h0 : (ν (-1) - θ (-1)) * (ν (-1) + θ (-1)) = 0 := by linear_combination hsq ν - hsq θ
    rcases mul_eq_zero.1 h0 with h | h
    · rw [sub_eq_zero.1 h, hsq θ]; ring
    · have hne' : θ⁻¹ * ν ≠ χ := fun h' => hne (by rw [← h', mul_inv_cancel_left])
      rw [hE.kill _ _ hne' (hform ν (eq_neg_of_add_eq_zero_left h))]
      ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiQuadAlt
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint

def fop {E : Type} [Field E] (k l : ℕ) (χ : ℕ → E) : Letter → Module.End E (ℕ → E)
  | Letter.T q =>
    { toFun := GlobalTheory.EisM.To k (χ q) q
      map_add' := fun a b => by funext n; simp only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, Pi.add_apply]; split_ifs <;> ring
      map_smul' := fun c a => by
        funext n; simp only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring }
  | Letter.U => { toFun := GlobalTheory.EisM.Uo l, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  | Letter.D d => χ d • 1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def th (X : Tower Ω ε) (A : ValuationSubring Ω) (N : ℕ) (j : Ω →+* Qbar l) (n : ℕ) (b : X.Fn l) : ℕ → Qbar l :=
  seqN 1 j (thN X A N l n 1 b)

def Std (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) : Prop :=
  (l : Ω) ∈ A.nonunits ∧ l ≠ 2 ∧ ¬ l ∣ N ∧ 5 ≤ N ∧ Odd w ∧ ∀ x ∈ A, ‖j x‖ ≤ 1

def FormP : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k N : ℕ) (χ : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (cc : ℕ → ℂ)
    (χE : ℕ → Qbar l) (ev : Letter → Qbar l), 1 ≤ k → GlobalTheory.EisM.EigF k N l χ t α B cc → (∀ d : ℕ, d.Coprime N → ι (χE d) = χ d) →
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ι (ev (Letter.T q)) = t q) → ι (ev Letter.U) = α →
    (∀ d : ℕ, d.Coprime N → ev (Letter.D d) = χE d) → ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l, ∀ a : ℕ → Qbar l,
    GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι (a i)) →
      GlobalTheory.EisM.lam B cc (fun i => ι (FreeAlgebra.lift (Qbar l) (fop k l χE) P a i)) =
        ι (FreeAlgebra.lift (Qbar l) ev P) * GlobalTheory.EisM.lam B cc fun i => ι (a i)

def FinP : Prop := CoefUb →
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k N : ℕ) (B : ℕ) (cc : ℕ → ℂ) (χE : ℕ → Qbar l) (c₀ : Coef l),
    ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l, ∃ (lam₀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (c : Coef l), c₀.O ≤ c.O ∧ FinSupp lam₀ ∧ FinSupp lam ∧
      (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) ∧ (∀ a, lam₀ a = ι.symm (GlobalTheory.EisM.lam B cc fun i => ι (a i))) ∧
      ∀ a, lam a = lam₀ (FreeAlgebra.lift (Qbar l) (fop k l χE) P a)

def ThLin : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l), Std A N w j → ∀ n : ℕ,
    ∃ Θ : (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (ℕ → Qbar l), ∀ b ∈ X.B N l w, ∀ i, Cg n (Θ ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) i) (th X A N j n b i)

def ThOp : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]), Std A N w j → ∀ (n : ℕ) (T : Letter) (b : X.Fn l),
    GlobalTheory.KZ.admitted N l T → InChi X N w χ b →
      ∀ i, Cg n (th X A N j n (X.op N l T b) i) (fop (w + 2) l (fun d => ((χ d : ℤ_[l]) : Qbar l)) T (th X A N j n b) i)

def ChiStab : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (N w : ℕ) (χ : ℕ → ℤ_[l]), l ≠ 2 → ¬ l ∣ N → 5 ≤ N → Odd w → ∀ (T : Letter) (b : X.Fn l),
    GlobalTheory.KZ.admitted N l T → InChi X N w χ b → InChi X N w χ (X.op N l T b)

def ThP : Prop := ThOp → ChiStab →
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (χ : ℕ → ℤ_[l]), Std A N w j → ∀ P ∈ admissibleLettersSubalgebra (Qbar l) N l,
    ∃ c : ℕ, ∀ n, c ≤ n → ∀ Θ : (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (ℕ → Qbar l),
      (∀ b ∈ X.B N l w, ∀ i, Cg n (Θ ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) i) (th X A N j n b i)) → ∀ b, InChi X N w χ b → ∀ i,
        Cg (n - c) (FreeAlgebra.lift (Qbar l) (fop (w + 2) l fun d => ((χ d : ℤ_[l]) : Qbar l)) P (th X A N j n b) i)
          (Θ (FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)) i)

def ChiQuad : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)) (χ : G ℚ Ω →* (Qbar l)ˣ), Nf e S A W → KillsMu l χ →
    ¬ l ∣ g.M → g.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ)) * (dt W)⁻¹ * χ)) →
    ∀ d : ℕ, d.Coprime g.M → g.χ d = 1 ∨ g.χ d = -1

end UpperTheory.V.Z.Kato.Joint

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.DistributionApply
section
noncomputable section

open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.EisM

namespace UpperTheory.V.Z.Kato.Joint.M3

variable {l : ℕ} [Fact l.Prime]

private def nu1 (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (κ : Qbar l) {n : ℕ}
    (β : Fin n → Qbar l) (t : Fin n → ℕ) (M : ℕ) : (ZMod (l ^ M) → Qbar l) →ₗ[Qbar l] Qbar l :=
  κ • ∑ i, β i • (nu0 ι e s u w α B c M).comp (LinearMap.funLeft (Qbar l) (Qbar l) fun y => (t i : ZMod (l ^ M)) * y)

private theorem distribution_apply (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (κ : Qbar l) {n : ℕ}
    (β : Fin n → Qbar l) (t : Fin n → ℕ) (M : ℕ) (g : ZMod (l ^ M) → Qbar l) :
    nu1 ι e s u w α B c κ β t M g = κ * ∑ i, β i * nu0 ι e s u w α B c M (fun y => g ((t i : ZMod (l ^ M)) * y)) := by
  simp only [nu1, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, LinearMap.comp_apply]
  rfl

private theorem q_lt : ‖(l : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem q_ne : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

private theorem small (C ε : ℝ) (hε : 0 < ε) : ∃ k : ℕ, ∀ r, k ≤ r → ‖(l : Qbar l)‖ ^ r * C < ε := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (l : Qbar l)) q_lt).mul_const C).eventually
    (gt_mem_nhds (by simpa using hε : 0 * C < ε))
  exact Filter.eventually_atTop.1 h

open Polynomial in
private theorem int_of_norm (x : Qbar l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)] at h
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic
    ((lifts_iff_coeff_lifts (f := algebraMap ℤ_[l] ℚ_[l]) (minpoly ℚ_[l] x)).mpr fun n => ⟨⟨_, h n⟩, rfl⟩) (minpoly.monic hi)
  exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem coef_of (K : IntermediateField ℚ_[l] (Qbar l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O := by
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] Qbar l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  exact ⟨⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x hx h => ⟨⟨x, hx⟩, (isIntegral_algHom_iff f hf).1 (int_of_norm _ h), rfl⟩⟩

private theorem distribution_integral {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ}
    {v : ℂ} (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) (hl : l ≠ 2) {n : ℕ} (β : Fin n → Qbar l) (t : Fin n → ℕ) :
    ∃ (cO : Coef l) (κ : Qbar l), κ ≠ 0 ∧ ∀ (M : ℕ) (x : ZMod (l ^ M)), nu1 ι e s u w α B c κ β t M (Pi.single x 1) ∈ cO.O := by
  obtain ⟨C, hC⟩ := eisensteinUnitFunctional_bounded H hs hl
  obtain ⟨E, hE, hF⟩ := exists_finiteExt_eisensteinUnitFunctional_mem H hs
  obtain ⟨k, hk⟩ := small (l := l) (∑ i, ‖β i‖ * C) 1 one_pos
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range β)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨cO, hO⟩ := coef_of (E ⊔ IntermediateField.adjoin ℚ_[l] (Set.range β))
  refine ⟨cO, (l : Qbar l) ^ k, pow_ne_zero _ q_ne, fun M x => ?_⟩
  rw [distribution_apply]
  refine hO _ (mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun i _ => mul_mem ?_ ?_)) ?_
  · exact le_sup_right (a := E) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  · refine le_sup_left (a := E) (hF _ _ fun y => ?_)
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · rw [norm_mul, norm_pow]
    refine le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)) (by positivity))
      (hk k le_rfl).le
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left (hC _ _ fun y => ?_) (norm_nonneg _)
    rw [Pi.single_apply]
    split_ifs <;> simp

private theorem riem0 {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ}
    {v : ℂ} (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) (hs' : s = (-1) ^ e * ψ (-1)) (hl : l ≠ 2)
    (φ : DirichletCharacter (Qbar l) l) (hφ : ∀ x, φ x = ι.symm (ψ⁻¹ x)) :
    ∃ C : ℝ, ∀ r, 1 ≤ r → ∀ t : ℕ, ¬ l ∣ t →
      ‖nu0 ι e s u w α B c r (fun y => if l ∣ ((t : ZMod (l ^ r)) * y).val then 0 else
          φ (((t : ZMod (l ^ r)) * y).val : ZMod l) * (((t : ZMod (l ^ r)) * y).val : Qbar l) ^ e) -
        φ t * (t : Qbar l) ^ e * ι.symm v‖ ≤ C * ‖(l : Qbar l) ^ r‖ := by
  obtain ⟨C, hC⟩ := eisensteinUnitFunctional_interpolation H hs hl
  refine ⟨C, fun r hr t ht => ?_⟩
  have hp : l.Prime := Fact.out
  have hT : ‖φ t * (t : Qbar l) ^ e‖ = 1 := by
    have hu : IsUnit (t : ZMod l) := (ZMod.isUnit_iff_coprime _ _).2 (hp.coprime_iff_not_dvd.2 ht).symm
    rw [norm_mul, norm_pow, norm_nat ht, one_pow, mul_one, ← hu.unit_spec, φ.unit_norm_eq_one]
  set T := φ t * (t : Qbar l) ^ e with hTd
  have hT0 : T ≠ 0 := norm_ne_zero_iff.1 (by rw [hT]; exact one_ne_zero)
  have key : ∀ x y : Qbar l, ‖T⁻¹ * x - y‖ = ‖x - T * y‖ := fun x y => by
    rw [show x - T * y = T * (T⁻¹ * x - y) by field_simp, norm_mul, hT, one_mul]
  have hφ' : ∀ x, φ⁻¹ x = ι.symm (ψ x) := fun x => by
    rw [MulChar.inv_apply_eq_inv', hφ, MulChar.inv_apply_eq_inv', map_inv₀, inv_inv]
  have hσ : ι.symm s * ι.symm s = 1 := by rw [← map_mul, hs, map_one]
  have hσn : ‖ι.symm s‖ = 1 := by rcases sgn_cases hs with rfl | rfl <;> simp
  have hσ' : φ (-1) * (-1) ^ e = ι.symm s := by
    have h1 : ψ⁻¹ (-1) = ψ (-1) := by
      rw [MulChar.inv_apply_eq_inv']
      exact inv_eq_of_mul_eq_one_right (by rw [← map_mul]; simp)
    rw [hφ, h1, hs']; simp [mul_comm]
  rw [← key, ← smul_eq_mul, ← map_smul]
  refine hC r hr _ _ (norm_nonneg _) fun a d ha hd y hy => ?_
  have htd : ¬ (l : ℤ) ∣ ((t * d : ℕ) : ℤ) := fun h => (hp.dvd_mul.1 (Int.natCast_dvd_natCast.1 h)).elim ht hd
  obtain ⟨h1, h2⟩ := UpperTheory.norm_character_pow_difference_estimate l r e φ ((t : ZMod (l ^ r)) * y) a ((t * d : ℕ) : ℤ) hr ha htd (by
    rw [mul_assoc, hy]; push_cast; rfl)
  obtain ⟨h3, h4⟩ := UpperTheory.norm_character_pow_difference_estimate l r e φ ((t : ZMod (l ^ r)) * -y) a (-((t * d : ℕ) : ℤ)) hr ha (by rwa [dvd_neg]) (by
    rw [mul_assoc, neg_mul, hy]; push_cast; ring)
  have hX : T * ι.symm (ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e) =
      φ (((t * d : ℕ) : ℤ) : ZMod l) * φ⁻¹ (a : ZMod l) * ((((t * d : ℕ) : ℤ) : Qbar l) / a) ^ e := by
    simp only [hTd, map_mul, map_pow, map_div₀, map_natCast, ← hφ, ← hφ', Int.cast_natCast, Nat.cast_mul, Int.cast_mul, div_pow,
      mul_pow]
    ring
  simp only [Pi.smul_apply, smul_eq_mul, if_neg h1, if_neg h3]
  refine ⟨by rw [key, hX]; exact h2, ?_⟩
  rw [mul_left_comm, key, hX]
  refine le_trans (le_of_eq ?_) h4
  rw [← one_mul ‖_ - φ ((-_ : ℤ) : ZMod l) * _ * _‖, ← hσn, ← norm_mul]
  congr 1
  rw [Int.cast_neg, Int.cast_neg, ← neg_one_mul (((t * d : ℕ) : ℤ) : ZMod l), map_mul, neg_div, neg_pow]
  linear_combination (φ (((t * d : ℕ) : ℤ) : ZMod l) * φ⁻¹ (a : ZMod l) * ((((t * d : ℕ) : ℤ) : Qbar l) / a) ^ e) *
    (ι.symm s * hσ' + hσ)

private theorem final (A : Qbar l) (hA : A ≠ 0) (C : ℝ) : ∃ n₀ r₁ : ℕ, ∀ r, r₁ ≤ r → ∀ S N : Qbar l,
    Cg (2 * r) S ((l : Qbar l) ^ r * N) → ‖N - A‖ ≤ C * ‖(l : Qbar l) ^ r‖ → ¬ Cg (n₀ + r) S 0 := by
  have h0 : 0 < ‖A‖ / 2 := by have := norm_pos_iff.2 hA; positivity
  obtain ⟨n₀, h1⟩ := small (l := l) 1 _ h0
  obtain ⟨r₁, h2⟩ := small (l := l) (1 + C) _ h0
  refine ⟨n₀, r₁, fun r hr S N hS hN hZ => ?_⟩
  unfold Cg at hS hZ
  have hq : 0 < ‖(l : Qbar l)‖ ^ r := pow_pos (norm_pos_iff.2 q_ne) _
  rw [sub_zero, norm_pow, pow_add] at hZ
  rw [norm_pow, two_mul, pow_add] at hS
  rw [norm_pow] at hN
  have h3 : ‖(l : Qbar l)‖ ^ r * ‖N‖ ≤ ‖S‖ + ‖S - (l : Qbar l) ^ r * N‖ := by
    rw [← norm_pow, ← norm_mul]
    simpa using norm_sub_le S (S - (l : Qbar l) ^ r * N)
  have h4 : ‖N‖ ≤ ‖(l : Qbar l)‖ ^ n₀ + ‖(l : Qbar l)‖ ^ r := le_of_mul_le_mul_left (by nlinarith) hq
  have h5 : ‖A‖ ≤ ‖N‖ + ‖N - A‖ := by simpa using norm_sub_le N (N - A)
  have := h1 n₀ le_rfl
  have := h2 r hr
  nlinarith

end UpperTheory.V.Z.Kato.Joint.M3

open UpperTheory.V.Z.Kato.Joint UpperTheory.V.Z.Kato.Joint.M3

theorem UpperTheory.V.Z.Kato.Joint.meas3 :
    UpperTheory.V.Z.Kato.Joint.Meas3 := by
  intro l _ ι e s u w ψ α B c v n β t hl he hs' H hv ht hS
  have hs : s * s = 1 := by
    have h1 : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul]; simp
    have h2 : ((-1 : ℂ) ^ e) * (-1) ^ e = 1 := by rw [← mul_pow]; simp
    rw [hs']
    linear_combination ψ (-1) * ψ (-1) * h2 + h1
  have hσ : ι.symm s * ι.symm s = 1 := by rw [← map_mul, hs, map_one]
  obtain ⟨cO, κ, hκ, hO⟩ := distribution_integral H hs hl β t
  obtain ⟨L, hL, hval⟩ := UpperTheory.exists_integral_powerSeries_of_bounded_distribution l cO (nu1 ι e s u w α B c κ β t) (fun M hM g g' h => by
    rw [distribution_apply, distribution_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eisensteinUnitFunctional_compat_succ H hs M hM]
    intro y
    simpa only [Nat.cast_mul] using h (t i * y)) fun M _ x => hO M x
  let φ : DirichletCharacter (Qbar l) l := ψ⁻¹.ringHomComp (ι.symm : ℂ →+* Qbar l)
  have hφ : ∀ x, φ x = ι.symm (ψ⁻¹ x) := fun x => rfl
  have hchar : ∀ m, 1 ≤ m → ∀ ψ' : DirichletCharacter (Qbar l) (l ^ m), ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) →
      Cg (2 * m) (∑ b : (ZMod (l ^ m))ˣ, ψ' b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))
        ((1 + ι.symm s * ψ' (-1)) / 2 * (κ * (∑ i, β i * ψ'⁻¹ (t i : ZMod (l ^ m))) *
          (∑ b : (ZMod (l ^ m))ˣ, ψ' b * z ^ (b : ZMod (l ^ m)).val) *
            ι.symm (mesMu (2 * e + 1) l u w α B c m (fun y => ι (ψ' y))))) := by
    intro m hm ψ' z hz
    have h := UpperTheory.gaussSum_twist_congr_of_measure l m (nu1 ι e s u w α B c κ β t m) L (fun g g' h => by
      rw [distribution_apply, distribution_apply]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => congrArg _ ?_)
      exact eisensteinUnitFunctional_congr_on_units ι e s u w α B c m _ _ fun x hx => h _ (((unit_iff hm _).2 (ht i)).mul hx)) (hval m hm) ψ' z hz.pow_eq_one
    have h2 : ∀ i, nu0 ι e s u w α B c m (fun y => ψ'⁻¹ ((t i : ZMod (l ^ m)) * y)) =
        ψ'⁻¹ (t i : ZMod (l ^ m)) * nu0 ι e s u w α B c m (fun y => ψ'⁻¹ y) := fun i => by
      rw [← smul_eq_mul (ψ'⁻¹ _) (nu0 ι e s u w α B c m _), ← map_smul]
      refine congrArg _ (funext fun y => ?_)
      rw [map_mul, Pi.smul_apply, smul_eq_mul]
    rw [distribution_apply] at h
    simp only [h2, eisensteinUnitFunctional_dirichletChar, ← mul_assoc, ← Finset.sum_mul] at h
    convert h using 1
    ring
  obtain ⟨C, hC⟩ := riem0 H hs hs' hl φ hφ
  have hA : κ * (∑ i, β i * (φ (t i : ZMod l) * (t i : Qbar l) ^ e)) * ι.symm v ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hκ fun h => hS ?_) (by simpa using hv)
    simpa [hφ, mul_assoc] using congrArg ι h
  obtain ⟨n₀, r₁, hfin⟩ := final _ hA (‖κ‖ * ∑ i, ‖β i‖ * C)
  refine ⟨cO, L, κ, φ, n₀, r₁, hκ, hL, fun x => by simp [hφ], fun m hm ψ' h z hz => ?_, fun m hm ψ' h z hz => ?_,
    fun r hr hr1 ξ hξ => ?_⟩
  · have := hchar m hm ψ' z hz
    rwa [h, hσ, add_self_div_two, one_mul] at this
  · have := hchar m hm ψ' z hz
    rwa [h, mul_neg, hσ, add_neg_cancel, zero_div, zero_mul] at this
  · refine hfin r hr _ _ (UpperTheory.restriction_to_units_congr_of_measure l r (nu1 ι e s u w α B c κ β t r) L (hval r hr1) ξ hξ
      (fun x => φ (x : ZMod l) * (x : Qbar l) ^ e) fun x => ?_) ?_
    · rw [norm_mul, norm_pow]
      exact mul_le_one₀ (φ.norm_le_one _) (by positivity)
        (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))
    · rw [distribution_apply, mul_assoc κ, ← mul_sub, norm_mul, mul_assoc ‖κ‖, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)) (norm_nonneg _)
      rw [mul_assoc (β i), ← mul_sub, norm_mul, mul_assoc ‖β i‖]
      exact mul_le_mul_of_nonneg_left (hC r hr1 _ (ht i)) (norm_nonneg _)

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrobAlt
section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.rhoFrob :
    UpperTheory.V.Z.Kato.Joint.RhoFrob := by
  intro l _ Ω _ _ _ ι e S A W g χ hN _ hatt ρ hρ
  have h : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Formalism.ConjugateSelfDual.Qbar l)) = _ := fun s =>
    (hρ s).trans (GlobalTheory.RhoAdm.untw_val' e W χ s).symm
  refine ⟨?_, fun V hV => GlobalTheory.RhoAdm.untw_irr e W χ hN.irr V fun s v hv => ?_⟩
  · obtain ⟨S0, hS0⟩ := GlobalTheory.RhoAdm.frob_trace_det ι e W g χ hatt
    refine ⟨S0, fun q hq hqS s hs => ?_⟩
    rw [h s]
    exact hS0 q hq hqS s hs
  · rw [← h s]
    exact hV s v hv
end

