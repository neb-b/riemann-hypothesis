module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1772
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCutoffContinuousCompactSupport
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem phiA_test : ∀ (F : Type) [Field F] [NumberField F] (G : Ainf F → ℝ) (a : (AF F)ˣ), Continuous G → HasCompactSupport G →
    Continuous (phiA G a) ∧ HasCompactSupport (phiA G a) := by
  intro F _ _ G a hc hs
  have h1 : (a : AF F).1 * ((a⁻¹ : (AF F)ˣ) : AF F).1 = 1 :=
    congrArg Prod.fst (a.mul_inv)
  have h2 : ((a⁻¹ : (AF F)ˣ) : AF F).1 * (a : AF F).1 = 1 :=
    congrArg Prod.fst (a.inv_mul)
  let m : Ainf F ≃ₜ Ainf F :=
    { toFun := fun x => (a : AF F).1 * x
      invFun := fun x => ((a⁻¹ : (AF F)ˣ) : AF F).1 * x
      left_inv := fun x => by simp only [← mul_assoc, h2, one_mul]
      right_inv := fun x => by simp only [← mul_assoc, h1, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  let e : (Unit → Ainf F) ≃ₜ Ainf F := (Homeomorph.funUnique Unit (Ainf F)).trans m
  have he : phiA G a = G ∘ e := by
    funext y
    rfl
  rw [he]
  exact ⟨hc.comp e.continuous, hs.comp_homeomorph e⟩

end GlobalTheory.CompanionTheory.BasePsi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwist
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

theorem carries_tw {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (e : GA E N → ℂ)
    (U U' : Submodule ℂ (Sm E N)) (z : ℂ) (h : Carries e U U') : Carries e (tw U z) (tw U' z) := by
  rintro _ ⟨ψ, hψ, rfl⟩
  obtain ⟨ψ', hψ', hx⟩ := h ψ hψ
  refine ⟨mulChi N (Model.absC E z) ψ', ⟨ψ', hψ', rfl⟩, fun x => ?_⟩
  simp only [LinearEquiv.coe_coe, mulChi_apply, hx, mul_assoc]

end GlobalTheory.CompanionTheory.LimV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistAbsoluteCharacter
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem carries_absFn_tw {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    (U : Submodule ℂ (Sm E N)) (z z' : ℂ) : Carries (absFn N (z' - z)) (tw U z) (tw U z') := by
  rintro φ ⟨ψ, hψ, rfl⟩
  refine ⟨mulChi N (GlobalTheory.CuspRep.Model.absC E z') ψ, ⟨ψ, hψ, rfl⟩, fun x => ?_⟩
  have e : ∀ s : ℂ, ((chiDet N (GlobalTheory.CuspRep.Model.absC E s) x : ℂˣ) : ℂ) =
      Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x)) := fun _ => rfl
  simp only [LinearEquiv.coe_coe, mulChi_apply, absFn]
  rw [e z', e (z' - z), e z, mul_left_comm, ← Complex.exp_add, ← add_mul, sub_add_cancel]

end GlobalTheory.CompanionTheory.LimV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHeckeCapelliOperators
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.CapCoeff

theorem coeff_mem_of_values {A : Type} [AddCommGroup A] [Module ℂ A] (W : Submodule ℂ A) (n : ℕ) (c : ℕ → A)
    (h : ∀ u : ℂ, ∑ k ∈ Finset.range n, u ^ k • c k ∈ W) : ∀ k < n, c k ∈ W := by
  intro k hk
  rw [← Submodule.Quotient.mk_eq_zero W]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_
  let p : ℂ[X] := ∑ i ∈ Finset.range n, Polynomial.C (f (Submodule.Quotient.mk (c i))) * Polynomial.X ^ i
  have hp : p = 0 := by
    refine Polynomial.funext fun u => ?_
    have h0 : (Submodule.Quotient.mk (∑ i ∈ Finset.range n, u ^ i • c i) : A ⧸ W) = 0 :=
      (Submodule.Quotient.mk_eq_zero W).2 (h u)
    have h1 := congrArg f h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Submodule.mkQ_apply, map_sum, map_sum, map_zero] at h1
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]
    rfl
  have hc := congrArg (fun q : ℂ[X] => q.coeff k) hp
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa [Finset.mem_range, hk] using hc

theorem qdet_coeffs {A : Type} [Ring A] [Algebra ℂ A] (W : Subalgebra ℂ A) (m : ℕ)
    (X : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ) (hW : ∀ u, Formalism.REAL.qdet X u ∈ W) :
    ∃ (c : ℕ → A) (t : ℂ), (∀ k, c k ∈ W) ∧ c (m + 1) = 1 ∧ c m = ∑ i, X i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet X (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  obtain ⟨c, t, h1, h2, h3⟩ := GlobalTheory.CapelliNext.qdet_shift_next_coeff A m X s
  have hm : ∀ k < m + 1 + 1, c k ∈ Subalgebra.toSubmodule W :=
    coeff_mem_of_values _ _ c fun u => by
      rw [← h3 u]
      exact hW _
  refine ⟨fun k => if k < m + 1 + 1 then c k else 0, t, fun k => ?_, ?_, ?_, fun u => ?_⟩
  · by_cases hk : k < m + 1 + 1
    · simp only [if_pos hk]
      exact hm k hk
    · simp only [if_neg hk]
      exact W.zero_mem
  · simpa only [if_pos (Nat.lt_succ_self (m + 1))] using h1
  · simpa only [if_pos (show m < m + 1 + 1 by omega)] using h2
  · rw [h3 u]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [if_pos (Finset.mem_range.1 hk)]

theorem qdet_commute_of {A : Type} [Ring A] [Algebra ℂ A] {n p : ℕ} (X : Fin n → Fin n → A) (Y : Fin p → Fin p → A)
    (h : ∀ i j k l, X i j * Y k l = Y k l * X i j) (u v : ℂ) :
    Formalism.REAL.qdet X u * Formalism.REAL.qdet Y v = Formalism.REAL.qdet Y v * Formalism.REAL.qdet X u := by
  have h1 : Formalism.REAL.qdet X u ∈ Subalgebra.centralizer ℂ (Set.range fun kl : Fin p × Fin p => Y kl.1 kl.2) := by
    refine GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem _ _ (fun i j => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨kl, rfl⟩
    exact (h i j kl.1 kl.2).symm
  have h2 : Formalism.REAL.qdet Y v ∈ Subalgebra.centralizer ℂ {Formalism.REAL.qdet X u} := by
    refine GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem _ _ (fun k l => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact ((Subalgebra.mem_centralizer_iff ℂ).1 h1 _ ⟨(k, l), rfl⟩).symm
  exact (Subalgebra.mem_centralizer_iff ℂ).1 h2 _ rfl

theorem qdet_commute_self {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (hX : Formalism.REAL.GlRel X)
    (u v : ℂ) : Formalism.REAL.qdet X u * Formalism.REAL.qdet X v = Formalism.REAL.qdet X v * Formalism.REAL.qdet X u := by
  have h : Formalism.REAL.qdet X v ∈ Subalgebra.centralizer ℂ {Formalism.REAL.qdet X u} := by
    refine GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem _ _ (fun c d => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact Formalism.REAL.qDetCentral A n X hX u c d
  exact (Subalgebra.mem_centralizer_iff ℂ).1 h _ rfl

theorem glRel_comp {A : Type} [Ring A] {n p : ℕ} {X : Fin n → Fin n → A} (hX : Formalism.REAL.GlRel X) {f : Fin p → Fin n}
    (hf : Function.Injective f) : Formalism.REAL.GlRel fun i j => X (f i) (f j) := by
  intro a b c d
  have h := hX (f a) (f b) (f c) (f d)
  simpa only [hf.eq_iff] using h

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem Eop_mem_of_lie {N : ℕ} (S : Subalgebra ℂ (Module.End ℂ (Sm E N))) (hL : ∀ X, lie E N X ∈ S) (τ : E →+* ℂ)
    (p q : Fin N) : Eop τ p q ∈ S :=
  Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (hL _) (Subalgebra.smul_mem _ (hL _) _)) _

def gens (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) : Set (Module.End ℂ (Sm E (r + s))) :=
  Set.range (fun p : (E →+* ℂ) × ℂ => GlobalTheory.CompanionTheory.CTFin.capR r s p.1 p.2) ∪
    Set.range (fun p : (E →+* ℂ) × ℂ => GlobalTheory.CompanionTheory.CTFin.capS r s p.1 p.2)

def capAlg (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) :
    Subalgebra ℂ (Module.End ℂ (Sm E (r + s))) :=
  Algebra.adjoin ℂ (gens E r s)

theorem capR_mem (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : GlobalTheory.CompanionTheory.CTFin.capR r s τ u ∈ capAlg E r s :=
  Algebra.subset_adjoin (Or.inl ⟨(τ, u), rfl⟩)

theorem capS_mem (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : GlobalTheory.CompanionTheory.CTFin.capS r s τ u ∈ capAlg E r s :=
  Algebra.subset_adjoin (Or.inr ⟨(τ, u), rfl⟩)

theorem capR_mul_capS (r s : ℕ) (τ τ' : E →+* ℂ) (u v : ℂ) :
    GlobalTheory.CompanionTheory.CTFin.capR r s τ u * GlobalTheory.CompanionTheory.CTFin.capS r s τ' v =
      GlobalTheory.CompanionTheory.CTFin.capS r s τ' v * GlobalTheory.CompanionTheory.CTFin.capR r s τ u := by
  by_cases h : τ = τ'
  · subst h
    exact (GlobalTheory.CompanionTheory.CTFin.CapFactor.capR_commute_capS r s τ u v).eq
  · unfold GlobalTheory.CompanionTheory.CTFin.capR GlobalTheory.CompanionTheory.CTFin.capS
    exact qdet_commute_of _ _ (fun i j k l => Eop_comm h _ _ _ _) _ _

theorem capR_mul_capR (r s : ℕ) (τ τ' : E →+* ℂ) (u v : ℂ) :
    GlobalTheory.CompanionTheory.CTFin.capR r s τ u * GlobalTheory.CompanionTheory.CTFin.capR r s τ' v =
      GlobalTheory.CompanionTheory.CTFin.capR r s τ' v * GlobalTheory.CompanionTheory.CTFin.capR r s τ u := by
  unfold GlobalTheory.CompanionTheory.CTFin.capR
  by_cases h : τ = τ'
  · subst h
    exact qdet_commute_self _ (glRel_comp (glRel_Eop τ) (Fin.castAdd_injective r s)) _ _
  · exact qdet_commute_of _ _ (fun i j k l => Eop_comm h _ _ _ _) _ _

theorem capS_mul_capS (r s : ℕ) (τ τ' : E →+* ℂ) (u v : ℂ) :
    GlobalTheory.CompanionTheory.CTFin.capS r s τ u * GlobalTheory.CompanionTheory.CTFin.capS r s τ' v =
      GlobalTheory.CompanionTheory.CTFin.capS r s τ' v * GlobalTheory.CompanionTheory.CTFin.capS r s τ u := by
  unfold GlobalTheory.CompanionTheory.CTFin.capS
  by_cases h : τ = τ'
  · subst h
    exact qdet_commute_self _ (glRel_comp (glRel_Eop τ) (Fin.natAdd_injective s r)) _ _
  · exact qdet_commute_of _ _ (fun i j k l => Eop_comm h _ _ _ _) _ _

theorem gens_comm (r s : ℕ) : ∀ a ∈ gens E r s, ∀ b ∈ gens E r s, a * b = b * a := by
  rintro a (⟨⟨τ, u⟩, rfl⟩ | ⟨⟨τ, u⟩, rfl⟩) b (⟨⟨τ', v⟩, rfl⟩ | ⟨⟨τ', v⟩, rfl⟩)
  · exact capR_mul_capR r s _ _ _ _
  · exact capR_mul_capS r s _ _ _ _
  · exact (capR_mul_capS r s _ _ _ _).symm
  · exact capS_mul_capS r s _ _ _ _

theorem capAlg_comm (r s : ℕ) : ∀ x ∈ capAlg E r s, ∀ y ∈ capAlg E r s, x * y = y * x := by
  intro x hx y hy
  letI := Algebra.isMulCommutative_adjoin ℂ (s := gens E r s)
    (fun a ha b hb _ => gens_comm (E := E) r s a ha b hb)
  exact setLike_mul_comm (s := Algebra.adjoin ℂ (gens E r s)) hx hy

theorem capAlg_le (r s : ℕ) (T : Subalgebra ℂ (Module.End ℂ (Sm E (r + s))))
    (hT : ∀ τ p q, Eop (a := r + s) τ p q ∈ T) : capAlg E r s ≤ T := by
  refine Algebra.adjoin_le ?_
  rintro _ (⟨⟨τ, u⟩, rfl⟩ | ⟨⟨τ, u⟩, rfl⟩)
  · exact GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem T _ (fun i j => hT τ _ _) _
  · exact GlobalTheory.CompanionTheory.CTFin.CapFactor.qdet_mem T _ (fun i j => hT τ _ _) _

theorem capAlg_commute_cap (r s : ℕ) {x : Module.End ℂ (Sm E (r + s))} (hx : x ∈ capAlg E r s) (τ : E →+* ℂ) (u : ℂ) :
    Commute (cap (a := r + s) τ u) x := by
  have hc : capAlg E r s ≤ Subalgebra.centralizer ℂ {cap (a := r + s) τ u} := by
    refine capAlg_le r s _ fun τ' p q => Eop_mem_of_lie _ (fun X => ?_) τ' p q
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact (commute_cap_lie τ u X).eq
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (hc hx) _ rfl

theorem capR_coeffs (m s : ℕ) (τ : E →+* ℂ) :
    ∃ (c : ℕ → Module.End ℂ (Sm E (m + 1 + s))) (t : ℂ),
      (∀ k, c k ∈ capAlg E (m + 1) s) ∧ c (m + 1) = 1 ∧
      c m = ∑ i : Fin (m + 1), Eop (a := m + 1 + s) τ (Fin.castAdd s i) (Fin.castAdd s i) + t • 1 ∧
      ∀ u : ℂ, GlobalTheory.CompanionTheory.CTFin.capR (m + 1) s τ (u - (s : ℂ) / 2) =
        ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  obtain ⟨c, t, h0, h1, h2, h3⟩ := qdet_coeffs (capAlg E (m + 1) s) m
    (fun i j : Fin (m + 1) => Eop (a := m + 1 + s) τ (Fin.castAdd s i) (Fin.castAdd s j))
    ((s : ℂ) / 2 - (((m + 1 : ℕ) : ℂ) - 1) / 2) (fun u => by
      have := capR_mem (E := E) (m + 1) s τ (u - (((m + 1 : ℕ) : ℂ) - 1) / 2)
      rwa [GlobalTheory.CompanionTheory.CTFin.capR, sub_add_cancel] at this)
  refine ⟨c, t, h0, h1, h2, fun u => ?_⟩
  rw [← h3 u, GlobalTheory.CompanionTheory.CTFin.capR]
  congr 1
  ring

theorem capS_coeffs (r n : ℕ) (τ : E →+* ℂ) :
    ∃ c : ℕ → Module.End ℂ (Sm E (r + (n + 1))),
      (∀ k, c k ∈ capAlg E r (n + 1)) ∧ c (n + 1) = 1 ∧
      ∀ u : ℂ, GlobalTheory.CompanionTheory.CTFin.capS r (n + 1) τ (u + (r : ℂ) / 2) =
        ∑ k ∈ Finset.range (n + 1 + 1), u ^ k • c k := by
  obtain ⟨c, t, h0, h1, -, h3⟩ := qdet_coeffs (capAlg E r (n + 1)) n
    (fun i j : Fin (n + 1) => Eop (a := r + (n + 1)) τ (Fin.natAdd r i) (Fin.natAdd r j))
    (-((r : ℂ) / 2) - (((n + 1 : ℕ) : ℂ) - 1) / 2) (fun u => by
      have := capS_mem (E := E) r (n + 1) τ (u - (((n + 1 : ℕ) : ℂ) - 1) / 2)
      rwa [GlobalTheory.CompanionTheory.CTFin.capS, sub_add_cancel] at this)
  refine ⟨c, h0, h1, fun u => ?_⟩
  rw [← h3 u, GlobalTheory.CompanionTheory.CTFin.capS]
  congr 1
  ring

theorem leftInv_closure {N r : ℕ} (F : Sm E N)
    (hF : ∀ (v : BlockIx N r → Ad E) (g : GA E N), F.1 (unip v * g) = F.1 g) :
    ∀ w ∈ Subgroup.closure (Set.range (unip : (BlockIx N r → Ad E) → GA E N)), ∀ g, F.1 (w * g) = F.1 g := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact hF v
  | one => intro g; rw [one_mul]
  | mul x y _ _ hx hy => intro g; rw [mul_assoc, hx, hy]
  | inv x _ hx => intro g; rw [← hx (x⁻¹ * g), mul_inv_cancel_left]

theorem capAlg_leftInv (r s : ℕ) {x : Module.End ℂ (Sm E (r + s))} (hx : x ∈ capAlg E r s) (F : Sm E (r + s))
    (hF : ∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g)
    (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)) : (x F).1 (unip v * g) = (x F).1 g := by
  have hc := capAlg_le (E := E) r s (GlobalTheory.SpehInfChar.leftInvAlg (Subgroup.closure
    (Set.range (unip : (BlockIx (r + s) r → Ad E) → GA E (r + s)))))
    (fun τ p q => GlobalTheory.SpehInfChar.Eop_mem_leftInvAlg _ τ p q)
  exact hc hx F (leftInv_closure F hF) (unip v) (Subgroup.subset_closure ⟨v, rfl⟩) g

theorem exists_coeffs : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s →
  ∃ (S : Subalgebra ℂ (Module.End ℂ (Sm E (r + s)))) (a b : (E →+* ℂ) → ℕ → Module.End ℂ (Sm E (r + s))) (t : (E →+* ℂ) → ℂ),
    (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
    (∀ x ∈ S, ∀ (τ : E →+* ℂ) (u : ℂ), Commute (cap (a := r + s) τ u) x) ∧
    (∀ x ∈ S, ∀ F : Sm E (r + s), (∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g) →
      ∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (x F).1 (unip v * g) = (x F).1 g) ∧
    (∀ τ k, a τ k ∈ S) ∧ (∀ τ k, b τ k ∈ S) ∧ (∀ τ, a τ r = 1) ∧ (∀ τ, b τ s = 1) ∧
    (∀ τ, a τ (r - 1) = ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i) + t τ • 1) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capR r s τ (u - (s : ℂ) / 2) = ∑ k ∈ Finset.range (r + 1), u ^ k • a τ k) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capS r s τ (u + (r : ℂ) / 2) = ∑ k ∈ Finset.range (s + 1), u ^ k • b τ k) := by
  intro E _ _ _ r s hr hs
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  choose a t ha0 ha1 ha2 ha3 using capR_coeffs (E := E) m (n + 1)
  choose b hb0 hb1 hb2 using capS_coeffs (E := E) (m + 1) n
  exact ⟨capAlg E (m + 1) (n + 1), a, b, t, capAlg_comm _ _, fun x hx τ u => capAlg_commute_cap _ _ hx τ u,
    fun x hx F hF v g => capAlg_leftInv _ _ hx F hF v g, ha0, hb0, ha1, hb1, ha2, ha3, hb2⟩

end GlobalTheory.CompanionTheory.CapCoeff

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSymmUnitaryChart
section
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.ChartSymm

theorem continuous_mat {D : D7} {n : ℕ} : Continuous (mat : G D n → Mx D (n + n) (n + n)) := by
  unfold GlobalTheory.StdUnn.mat
  exact Continuous.comp' Units.continuous_val continuous_induced_dom

private theorem gram_conjTranspose_eq_self {D : D7} (S : HSp D) :
    (Formalism.BasicNotions.HSpace.gram S).conjTranspose = Formalism.BasicNotions.HSpace.gram S := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Formalism.BasicNotions.HSpace.gram]
  exact S.herm.eq (S.frame j) (S.frame i)

private theorem fromRows_gram_mul_fromCols_eq_one_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : D.host.E)
    (hμ : μ ≠ 0) :
    Matrix.fromRows (d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S)
        (μ⁻¹ • (d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S)) *
      Matrix.fromCols d.e (μ • d.e') = 1 := by
  have h1 : d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e = 1 := d.e'e
  have h0 : d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e = 0 := d.ee
  have h0' : d.e'.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e' = 0 := d.e'e'
  have h2 : d.e.conjTranspose * Formalism.BasicNotions.HSpace.gram S * d.e' = 1 := by
    have h := congrArg Matrix.conjTranspose h1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose_eq_self,
      Matrix.conjTranspose_one] at h
    rw [Matrix.mul_assoc]
    exact h
  rw [Matrix.fromRows_mul_fromCols]
  simp only [Matrix.mul_smul, Matrix.smul_mul, h1, h0, h0', h2, smul_zero, smul_smul,
    inv_mul_cancel₀ hμ, mul_inv_cancel₀ hμ, one_smul, Matrix.fromBlocks_one]

theorem continuous_symm : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ (κ : GA D (dblSp A) ≃* G D A.rank), IsChart A μ κ →
    Continuous κ.symm := by
  intro D A μ hμ κ hκ
  have hL : ((Matrix.fromRows ((dblDec A).e'.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A))
        (μ⁻¹ • ((dblDec A).e.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A)))).submatrix
          finSumFinEquiv.symm id) * Tm A μ = 1 := by
    show _ * (Matrix.fromCols (dblDec A).e (μ • (dblDec A).e')).submatrix id finSumFinEquiv.symm = 1
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, fromRows_gram_mul_fromCols_eq_one_of_hypDec _ μ hμ.1,
      Matrix.submatrix_one_equiv]
  have hR := mul_eq_one_comm.mp hL
  set L := (Matrix.fromRows ((dblDec A).e'.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A))
        (μ⁻¹ • ((dblDec A).e.conjTranspose * Formalism.BasicNotions.HSpace.gram (dblSp A)))).submatrix
          finSumFinEquiv.symm id with hLdef
  have hTP : rat (Tm A μ) * rat L = (1 : Mx D (A.rank + A.rank) (A.rank + A.rank)) := by
    show (incA D).mapMatrix (Tm A μ) * (incA D).mapMatrix L = 1
    rw [← map_mul, hR, map_one]
  have key : ∀ h : G D A.rank, mt (dblSp A) (κ.symm h) = rat (Tm A μ) * mat h * rat L := by
    intro h
    have e := hκ (κ.symm h)
    rw [MulEquiv.apply_symm_apply] at e
    calc mt (dblSp A) (κ.symm h) = mt (dblSp A) (κ.symm h) * (rat (Tm A μ) * rat L) := by
          rw [hTP, Matrix.mul_one]
      _ = (mt (dblSp A) (κ.symm h) * rat (Tm A μ)) * rat L := by rw [Matrix.mul_assoc]
      _ = rat (Tm A μ) * mat h * rat L := by rw [← e]
  have hind : Topology.IsInducing (fun g : GA D (dblSp A) => matHom (dblSp A) g) := ⟨rfl⟩
  have hmi : Continuous (fun h : G D A.rank => mat h⁻¹) := by
    unfold GlobalTheory.StdUnn.mat
    simp only [map_inv]
    exact Units.continuous_coe_inv.comp continuous_induced_dom
  rw [hind.continuous_iff, Units.continuous_iff]
  constructor
  · have hf : (Units.val ∘ (fun g : GA D (dblSp A) => matHom (dblSp A) g) ∘ κ.symm) =
        fun h => rat (Tm A μ) * mat h * rat L := by
      funext h
      exact key h
    rw [hf]
    exact (continuous_const.matrix_mul continuous_mat).matrix_mul continuous_const
  · have hf : (fun h : G D A.rank => (((fun g : GA D (dblSp A) => matHom (dblSp A) g) ∘ κ.symm) h)⁻¹.val) =
        fun h => rat (Tm A μ) * mat h⁻¹ * rat L := by
      funext h
      simp only [Function.comp_apply]
      rw [← map_inv (matHom (dblSp A)), ← map_inv κ.symm]
      exact key h⁻¹
    rw [hf]
    exact (continuous_const.matrix_mul hmi).matrix_mul continuous_const

end GlobalTheory.CompanionTheory.ChartSymm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDeterminingSet
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem exists_finset_separating_points {A : Type} (W : Submodule ℂ (A → ℂ)) :
    FiniteDimensional ℂ W → ∃ S : Finset A, ∀ w ∈ W, (∀ a ∈ S, w a = 0) → w = 0 :=
  _root_.Bl.FirstLemmaH.goal1 W

end GlobalTheory.CompanionTheory.LimV
end

