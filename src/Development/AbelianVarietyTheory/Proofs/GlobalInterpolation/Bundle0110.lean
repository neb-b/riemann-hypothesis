module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0080
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.FewBadPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0098
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Formalism.GL3MeanSquares.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedAreaClassInvariant
section
noncomputable section

namespace GlobalTheory.ConjEquidistrib

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors Pointwise


open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates in
theorem fixesK_conjEmb_iff (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) :
    FixesK D M (conjEmb M ρ) ↔ ¬ FixesK D M ρ := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let σM : D.host.K →+* M := σ.codRestrict M hm
  have hsq := D.host.sqd_sq
  let b : D.host.K :=
    ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hb : b ^ 2 = -(D.host.d : D.host.K) := by
    apply Subtype.ext
    simpa using hsq
  have hall : ∀ ψ : D.host.K →+* ℂ, ψ b ^ 2 = -(D.host.d : ℂ) := fun ψ => by
    rw [← map_pow, hb, map_neg, map_natCast]
  have hcj : ∀ ψ : D.host.K →+* ℂ, (starRingEnd ℂ) (ψ b) = -ψ b := fun ψ => by
    have h1 : (ψ b) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [hall, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;>
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal] <;> ring
  have hne : σ b ≠ 0 := by
    intro h0
    have := hall σ
    rw [h0] at this
    have hd : (0 : ℂ) ≠ -(D.host.d : ℂ) := by
      rw [ne_eq, eq_comm, neg_eq_zero, Nat.cast_eq_zero]
      exact D.host.hyp.2.1.ne_zero
    exact hd (by simpa using this)
  have key : ∀ ρ' : M →ₐ[ℚ] ℂ, ρ' (σM b) = σ b → FixesK D M ρ' := fun ρ' h x y hy => by
    have : ((ρ' : M →+* ℂ).comp σM).toRatAlgHom = σ.toRatAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K)
        (s := {D.host.sqd}) rfl fun x hx => ?_
      obtain rfl : x = _ := hx
      exact h
    have h2 : ρ' (σM x) = σ x := DFunLike.congr_fun this x
    have hyx : y = σM x := Subtype.ext hy
    rw [hyx]
    exact h2
  have back : ∀ ρ' : M →ₐ[ℚ] ℂ, FixesK D M ρ' → ρ' (σM b) = σ b := fun ρ' h => h b (σM b) rfl
  have h1 : ρ (σM b) ^ 2 = σ b ^ 2 := (hall ((ρ : M →+* ℂ).comp σM)).trans (hall σ).symm
  constructor
  · intro hc hf
    have e1 := back _ hc
    have e2 := back _ hf
    rw [conjEmb_apply, e2, hcj] at e1
    exact hne (by linear_combination -e1 / 2)
  · intro hf
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact absurd (key ρ h) hf
    · refine key _ ?_
      rw [conjEmb_apply, h, map_neg, hcj, neg_neg]

theorem fixK_of_fixesK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) (h : GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates.FixesK D M ρ) :
    Formalism.MainNotions.StandardLatticesGL3.FixK D M ρ := fun a => by
  refine ⟨hm a, ?_⟩
  unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM
  rw [dite_eq_left (hm a)]
  exact h a _ rfl

open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates

end GlobalTheory.ConjEquidistrib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ObjOnNarrowOfObjectsExist
section
noncomputable section

namespace GlobalTheory.ObjExCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory NumberField GlobalTheory.EX GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

variable {R : Ranks}

theorem one_lt_condE (H : Host R) : 1 < condE H := by
  unfold condE
  exact lt_of_lt_of_le H.hyp.2.1.one_lt (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))

theorem norm_modEq (H : Host R) (π : 𝓞 H.E) {T N : ℕ} (hN : N ≠ 0)
    (hn : (π : H.E) * H.conj (π : H.E) = (T : H.E)) (h1 : π - 1 ∈ Ideal.span {((N : ℕ) : 𝓞 H.E)}) :
    T ≡ 1 [MOD N] := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  have hyi : IsIntegral ℤ (a : H.E) := RingOfIntegers.isIntegral_coe a
  have hπ : (π : H.E) = 1 + N * (a : H.E) := by
    have := congrArg (fun z : 𝓞 H.E => (z : H.E)) ha
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    linear_combination -this
  have hci : IsIntegral ℤ (H.conj (a : H.E)) := hyi.map ((H.conj : H.E →+* H.E).toIntAlgHom)
  rw [hπ, map_add (f := _), map_mul, map_one, map_natCast] at hn
  set z : H.E := a + H.conj (a : H.E) + N * (a * H.conj (a : H.E)) with hz
  have hzi : IsIntegral ℤ z :=
    (hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := H.E) N).mul (hyi.mul hci))
  have hM0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have h4 : z = algebraMap ℚ H.E (((T : ℚ) - 1) / N) := by
    have hM0' : (N : H.E) ≠ 0 := by exact_mod_cast hN
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]
    linear_combination hn
  rw [h4, isIntegral_algebraMap_iff ] at hzi
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi
  have h5 : (((T : ℤ) - ((1 : ℕ) : ℤ) : ℤ) : ℚ) = ((N * n : ℤ) : ℚ) := by
    have : (n : ℚ) = ((T : ℚ) - 1) / N := by simpa using hn'
    push_cast
    rw [this]
    field_simp
  exact (Nat.modEq_iff_dvd.2 ⟨n, by exact_mod_cast h5⟩).symm

theorem T_modEq (D : D7) (u : D.what₂.Word) : (D.mem u).A.T ≡ 1 [MOD condE D.host] := by
  obtain ⟨π, -, h2, h3⟩ := D.T_norm u
  have h0 : condE D.host * (D.host.g 0 * D.host.g 1) ^ 2 ≠ 0 :=
    Nat.mul_ne_zero (by have := one_lt_condE D.host; omega)
      (pow_ne_zero _ (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  exact (norm_modEq D.host π h0 h2 h3).of_mul_right _

end GlobalTheory.ObjExCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFacts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.LatFin


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.MomT.LatFin.per_lattice_facts : ∀ (X : _root_.Formalism.L2.Col.Fields) (A : _root_.Formalism.L2.Ker.Amb X) (a b : ℕ)
    (N : Submodule (𝓞 X.E) (_root_.Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (_root_.Formalism.L2.Col.Sp X.E b)),
    A.AA.FG → A.AA ≠ ⊥ → _root_.Formalism.L2.Col.IsSdLat N → _root_.Formalism.L2.Col.IsSdLat N' → (_root_.GlobalTheory.MomT.per A N N').FG ∧
    (∀ x : _root_.Formalism.L2.Col.HomE X.E a b, ∃ n : ℕ, 0 < n ∧ (n : X.E) • x ∈ _root_.GlobalTheory.MomT.per A N N') ∧
    (∀ r : 𝓞 X.E, r ≠ 0 → (_root_.GlobalTheory.MomT.smulLat (r : X.E)
      (_root_.GlobalTheory.MomT.per A N N')).toAddSubgroup.relIndex
        (_root_.GlobalTheory.MomT.per A N N').toAddSubgroup ≠ 0) ∧
    ∀ P : HeightOneSpectrum (𝓞 X.E), _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A.AA =
      _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) → ∀ y : _root_.Formalism.L2.Col.HomE X.E a b,
      y ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (_root_.GlobalTheory.MomT.per A N N') ↔
        ∀ v ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, y v ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' := by
  intro X A a b N N' hAfg hA hN hN'
  have full_of_sd {n : ℕ} {L : Submodule (𝓞 X.E) (Sp X.E n)}
      (hL : IsSdLat L) : Submodule.IsFullLattice X.E L := by
    let := hL.1
    refine { span_eq_top := ?_ }
    let W := Submodule.span X.E (L : Set (Sp X.E n))
    change W = ⊤
    by_contra hW
    let e : Sp X.E n ≃ₗ⋆[X.E] Sp X.E n := starLinearEquiv X.E
    let g : Sp X.E n →ₗ[X.E] Module.Dual X.E W :=
      (LinearMap.domRestrict' W).comp ((hStd X.E n).comp e.toLinearMap)
    have hdim : Module.finrank X.E (Module.Dual X.E W) < Module.finrank X.E (Sp X.E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (c : X.E) : c • e x ∈ L := by
      rw [← hL.2, dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd X.E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual X.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : X.E →ₗ[𝓞 X.E] L :=
      ((LinearMap.toSpanSingleton X.E _ (e x)).restrictScalars (𝓞 X.E)).codRestrict L hsmul
    let : Module.Finite (𝓞 X.E) L := Module.Finite.iff_fg.mpr hL.1.fg
    let : Module.Finite (𝓞 X.E) X.E := Module.Finite.of_injective i fun c d hcd =>
      smul_left_injective X.E (fun hz => hx₀ (e.map_eq_zero_iff.mp hz)) (congrArg Subtype.val hcd)
    exact RingOfIntegers.not_isField X.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 X.E) X.E) (Field.toIsField X.E))
  have hNfull := full_of_sd hN
  have hN'full := full_of_sd hN'
  obtain ⟨hNl, -⟩ := hN
  obtain ⟨hN'l, -⟩ := hN'
  have hfull : _root_.GlobalTheory.ThetaMove.Full (_root_.Formalism.L2.Ker.perO A.AA N N') :=
    _root_.GlobalTheory.ThetaMove.PeriodComp.full A.AA N N' hNl.fg hN'full hA
  have hfg : (_root_.GlobalTheory.MomT.per A N N').FG :=
    _root_.GlobalTheory.ThetaMove.VolumePos.perO_fg hAfg
      (_root_.GlobalTheory.ThetaMove.VolumePos.homO_fg hNl.fg hN'l.fg (by
        let := hNfull
        exact Submodule.IsFullLattice.span_eq_top))
  have hmult : ∀ x : _root_.Formalism.L2.Col.HomE X.E a b, ∃ n : ℕ, 0 < n ∧
      (n : X.E) • x ∈ _root_.GlobalTheory.MomT.per A N N' := by
    intro x
    obtain ⟨n, hn, hx⟩ := hfull x
    refine ⟨n, hn, ?_⟩
    unfold _root_.GlobalTheory.MomT.per
    rw [Nat.cast_smul_eq_nsmul]
    rwa [Nat.cast_smul_eq_nsmul] at hx
  refine ⟨hfg, hmult, ?_, ?_⟩
  · intro r hr
    refine _root_.GlobalTheory.ThetaMove.VolumePos.relIndex_ne_zero ?_ hfg
    intro x
    obtain ⟨n, hn, hx⟩ := hmult ((r : X.E)⁻¹ • x)
    refine ⟨n, hn, ?_⟩
    rw [_root_.GlobalTheory.MomT.mem_smulLat]
    refine ⟨_, hx, ?_⟩
    have hr' : (r : X.E) ≠ 0 := by exact_mod_cast hr
    rw [smul_smul, smul_smul, mul_comm (r : X.E), mul_assoc, mul_inv_cancel₀ hr', mul_one,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  · intro P hP y
    unfold _root_.GlobalTheory.MomT.per
    constructor
    · intro hy v hv
      obtain ⟨s, hs, hsy⟩ := (_root_.Formalism.L2.Col.mem_locP P _ y).mp hy
      refine _root_.GlobalTheory.MomT.IdxBound.mem_localization_of_smul_mem P N' hs ?_
      simpa using _root_.GlobalTheory.MomT.IdxBound.per_apply_mem hP hsy hv
    · intro hy
      exact _root_.GlobalTheory.MomT.IdxBound.mem_localization_perO hP hNl.fg fun v hv =>
        hy v (_root_.GlobalTheory.ThetaMove.mem_localization_of_mem P hv)

end GlobalTheory.MomT.LatFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PowEqOfPartEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC.TameGen

theorem part_pow {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G} (hx : IsOfFinOrder x) :
    ∃ a : ℕ, Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  set a := (orderOf x).factorization l with ha
  set M := orderOf x / l ^ a with hM
  have hmul : l ^ a * M = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
  have hM0 : M ≠ 0 := (Nat.ordCompl_pos l hn).ne'
  haveI : NeZero M := ⟨hM0⟩
  set u := (((l ^ a : ℕ) : ZMod M)⁻¹).val with hu
  have hz : Formalism.CyclotomicNorms.primeToPart l x = x ^ (l ^ a * u) := rfl
  have hone : (x ^ (l ^ a)) ^ M = 1 := by rw [← pow_mul, hmul, pow_orderOf_eq_one]
  have hmod : l ^ a * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow_left a hcop.symm)
  refine ⟨a, ?_⟩
  rw [hz, ← pow_mul, mul_comm, pow_mul]
  have := pow_eq_pow_of_modEq hmod hone
  rwa [pow_one] at this

theorem pow_eq_of_part_eq {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x y : G} (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) (h : Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l y) :
    ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a) := by
  obtain ⟨a, ha⟩ := part_pow hl hx
  obtain ⟨b, hb⟩ := part_pow hl hy
  refine ⟨a + b, ?_⟩
  have h1 : x ^ (l ^ (a + b)) = Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ (a + b)) := by
    rw [pow_add, pow_mul, pow_mul, ha]
  have h2 : y ^ (l ^ (a + b)) = Formalism.CyclotomicNorms.primeToPart l y ^ (l ^ (a + b)) := by
    rw [add_comm, pow_add, pow_mul, pow_mul, hb]
  rw [h1, h2, h]

def expo {m : ℕ} : Option (Fin m × Bool) → ℤ
  | none => 0
  | some (j, true) => (j.1 : ℤ) + 1
  | some (j, false) => -((j.1 : ℤ) + 1)

theorem expo_inj {m : ℕ} : Function.Injective (expo (m := m)) := by
  rintro (_ | ⟨i, _ | _⟩) (_ | ⟨j, _ | _⟩) h <;> simp only [expo] at h <;>
    first
    | rfl
    | (exfalso; omega)
    | (have : i = j := Fin.ext (by omega); rw [this])

theorem expo_bound {m : ℕ} (o : Option (Fin m × Bool)) : -(m : ℤ) ≤ expo o ∧ expo o ≤ m := by
  rcases o with (_ | ⟨i, _ | _⟩) <;> simp only [expo]
  · omega
  · have := i.2; omega
  · have := i.2; omega

theorem tameList_eq {g m : ℕ} (w : (ZMod g)ˣ) (o : Option (Fin m × Bool)) :
    DC.tameList (fun j : Fin m => w ^ (2 * (j.1 + 1))) o = w ^ (2 * expo o) := by
  rcases o with (_ | ⟨i, _ | _⟩) <;> simp only [expo, DC.tameList]
  · simp
  · rw [mul_neg, zpow_neg, ← zpow_natCast]; push_cast; rfl
  · rw [← zpow_natCast]; push_cast; rfl

theorem dvd_of_pow_eq {g m : ℕ} (w : (ZMod g)ˣ) {o o' : Option (Fin m × Bool)} (hne : o ≠ o') (k : ℕ)
    (h : (w ^ (2 * expo o)) ^ k = (w ^ (2 * expo o')) ^ k) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 4 * m ∧ orderOf w ∣ D * k := by
  have h1 : expo o ≠ expo o' := fun e => hne (expo_inj e)
  have b1 := expo_bound o
  have b2 := expo_bound o'
  refine ⟨(2 * expo o' - 2 * expo o).natAbs, by omega, by omega, ?_⟩
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, zpow_eq_zpow_iff_modEq] at h
  have h2 := h.dvd
  rw [← sub_mul, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast] at h2
  exact h2

theorem tameDistinct_gen : ∀ (r g m : ℕ) [Fact g.Prime] (w : (ZMod g)ˣ), orderOf w = g - 1 → 4 * (m : ℝ) * (g : ℝ) ^ ((1 : ℝ) / 4) < (g : ℝ) - 1 → 1 ≤ r → DC.TameDistinct r g (fun j : Fin m => w ^ (2 * (j.1 + 1))) := by
  intro r g m hg w hw hlt hr
  have hg2 : 2 ≤ g := hg.out.two_le
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hcast : ((g - 1 : ℕ) : ℝ) = (g : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hq : (1 : ℝ) ≤ (g : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hgR (by norm_num)
  have hm0 : (0 : ℝ) ≤ 4 * (m : ℝ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro o o' h
    by_contra hne
    rw [tameList_eq, tameList_eq] at h
    obtain ⟨D, hD0, hD, hdvd⟩ := dvd_of_pow_eq w hne 1 (by rw [h])
    rw [mul_one, hw] at hdvd
    have h1 : g - 1 ≤ 4 * m := (Nat.le_of_dvd hD0 hdvd).trans hD
    have h2 : ((g - 1 : ℕ) : ℝ) ≤ ((4 * m : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hcast] at h2
    push_cast at h2
    nlinarith
  · intro l hl hB o o' h
    by_contra hne
    apply hB
    simp only [tameList_eq] at h
    have hfin : ∀ u : (ZMod g)ˣ, IsOfFinOrder (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (u : ZMod g)) := by
      intro u
      exact (((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom (ZMod g))).isOfFinOrder
        (isOfFinOrder_of_finite u))
    obtain ⟨a, ha⟩ := pow_eq_of_part_eq hl (hfin _) (hfin _) h
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at ha
    have ha' := Units.ext ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective ha)
    obtain ⟨D, hD0, hD, hdvd⟩ := dvd_of_pow_eq w hne _ ha'
    rw [hw] at hdvd
    have hn : g - 1 ≠ 0 := by omega
    set v := (g - 1).factorization l with hv
    set M := (g - 1) / l ^ v with hM
    have hmul : l ^ v * M = g - 1 := Nat.ordProj_mul_ordCompl_eq_self _ _
    have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
    have hMD : M ∣ D := (Nat.Coprime.pow_right a hcop).dvd_of_dvd_mul_right
      ((Dvd.intro_left _ hmul).trans hdvd)
    have hMle : M ≤ 4 * m := (Nat.le_of_dvd hD0 hMD).trans hD
    have h1 : g - 1 ≤ 4 * m * l ^ v := by
      rw [← hmul, mul_comm]; exact Nat.mul_le_mul_right _ hMle
    have h2 : ((g - 1 : ℕ) : ℝ) ≤ ((4 * m * l ^ v : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hcast] at h2
    push_cast at h2
    have h3 : (g : ℝ) ^ ((1 : ℝ) / 4) < (l : ℝ) ^ v := lt_of_mul_lt_mul_left (hlt.trans_le h2) hm0
    have h4 : ((g : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 < ((l : ℝ) ^ v) ^ 4 :=
      pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
    have h5 : ((g : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = g := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    rw [h5, ← pow_mul, mul_comm] at h4
    refine Or.inr ⟨1, le_rfl, hr, hl, ?_⟩
    rw [pow_one, Nat.padicValNat_def, ← Nat.factorization_def _ hl, ← hv]
    exact_mod_cast h4
  · intro j
    exact ⟨w ^ (j.1 + 1), by rw [← pow_add, ← two_mul]⟩

end GlobalTheory.EX.DC.TameGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmallPrimeOneOfPrimesRel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem smallPrimeOne_of_primesRel : GlobalTheory.Lin.PrimesRel → SmallPrimeOne := by
  intro h
  obtain ⟨C₀, Cr, cr, c, h0, h1, h2, h3, H⟩ := GlobalTheory.Lin.primesAPInterval_of_primesRel h
  obtain ⟨s, hsC, hs21, hsr⟩ : ∃ s : ℝ, C₀ ≤ s ∧ 21 ≤ s ∧ 200 * Cr / cr ≤ s :=
    ⟨max C₀ (max 21 (200 * Cr / cr)), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _), le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hss : s ≤ s ^ 2 := by nlinarith
  have hexp : Cr * Real.exp (-cr * s) ≤ 1 / 200 := by
    have e1 : 200 * Cr ≤ cr * s := by
      rw [div_le_iff₀ h2] at hsr; linarith
    have e2 := Real.add_one_le_exp (cr * s)
    have e3 : 0 < Real.exp (cr * s) := Real.exp_pos _
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ e3 (by norm_num)]
    linarith
  refine ⟨3 * s ^ 2 + 1, by nlinarith, ?_⟩
  intro M hM
  rcases Nat.eq_or_lt_of_le hM with rfl | hM3
  · refine ⟨3, Nat.prime_three, by norm_num, ?_⟩
    have e1 : ((2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (3 * s ^ 2 + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    refine le_trans ?_ e1
    norm_num
  have hm3 : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hB0 : (0 : ℝ) < 4 * (M : ℝ) := by linarith
  have hB1 : (1 : ℝ) ≤ 4 * (M : ℝ) := by linarith
  have hlB : 1 ≤ Real.log (4 * (M : ℝ)) := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  set Y : ℝ := (4 * (M : ℝ)) ^ (s ^ 2) with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hB0 _
  have hlY : Real.log Y = s ^ 2 * Real.log (4 * (M : ℝ)) := Real.log_rpow hB0 _
  have hlY2 : s ^ 2 ≤ Real.log Y := by rw [hlY]; nlinarith [sq_nonneg s]
  have hlY0 : 0 < Real.log Y := by linarith
  have hrho : Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr (4 * M) Y ≤ 1 / 100 := by
    unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    have a1 : Real.exp (-cr * Real.log Y / Real.log (4 * (M : ℝ))) ≤ Real.exp (-cr * s) := by
      apply Real.exp_le_exp.2
      rw [hlY, ← mul_assoc, mul_div_assoc, div_self (by linarith), mul_one]
      nlinarith
    have a2 : Real.exp (-cr * Real.sqrt (Real.log Y)) ≤ Real.exp (-cr * s) := by
      apply Real.exp_le_exp.2
      have : s ≤ Real.sqrt (Real.log Y) := Real.le_sqrt_of_sq_le hlY2
      nlinarith
    have b1 := mul_le_mul_of_nonneg_left a1 h1.le
    have b2 := mul_le_mul_of_nonneg_left a2 h1.le
    linarith
  have h7 : (4 * (M : ℝ)) ^ (7 : ℝ) ≤ 1 * Y ^ ((1 : ℝ) / 3) := by
    rw [one_mul, hY, ← Real.rpow_mul hB0.le]
    exact Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have hc := H M 1 hM3 (Nat.coprime_one_left M) Y 1
    (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)) le_rfl hrho h7
  have hpos : 0 < c * 1 * (4 * (M : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y := by
    have := Real.rpow_pos_of_pos hB0 (-6 : ℝ)
    positivity
  have hcard := lt_of_lt_of_le hpos hc
  rw [Nat.cast_pos, Finset.card_pos] at hcard
  obtain ⟨p, hp⟩ := hcard
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨-, hp2⟩, hpp, hpm⟩ := hp
  refine ⟨p, hpp, ?_, ?_⟩
  · have : p % M = 1 % M := hpm
    rw [this]; exact Nat.mod_eq_of_lt (by omega)
  · have e1 : (p : ℝ) ≤ Y * (1 + 1) :=
      le_trans (Nat.cast_le.2 hp2) (Nat.floor_le (by positivity))
    have hM0 : (0 : ℝ) < M := by linarith
    have e2 : Y ≤ (M : ℝ) ^ (3 * s ^ 2) := by
      rw [Real.rpow_mul hM0.le]
      apply Real.rpow_le_rpow hB0.le _ (by positivity)
      have : (M : ℝ) ^ (3 : ℝ) = (M : ℝ) ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast (M : ℝ) 3
      rw [this]
      have : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
      nlinarith
    rw [Real.rpow_add hM0, Real.rpow_one]
    nlinarith

end GlobalTheory.EX
end

