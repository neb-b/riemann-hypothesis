module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldSplitsInOfIsRayPrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem not_isUnit_natCast {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) : ¬ IsUnit (p : 𝓞 K) := by
  intro h
  have : IsLocalHom (algebraMap ℤ (𝓞 K)) := Algebra.IsIntegral.isLocalHom _ _
  rw [← map_natCast (algebraMap ℤ (𝓞 K))] at h
  exact (Nat.prime_iff_prime_int.1 hp).not_unit (isUnit_of_map_unit _ _ h)

theorem rayField_splitsIn_of_isRayPrime (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M)
    (hf : FiniteDimensional ℚ M) :
    letI := GlobalTheory.ParRay.algK D jE h
    haveI := GlobalTheory.ParRay.nfOf hf
    GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) →
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn M p := by
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  intro hM p hp
  obtain ⟨hpp, π, hπK, hπi, hπc, σ, hσ⟩ := hp
  have hc0 : ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) ≠ 0 := by
    exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
  let φ : D.host.K →+* Qb := jE.comp (D.host.K.val : D.host.K →+* D.host.E)
  have hφ : Function.Injective φ := jE.injective.comp Subtype.val_injective
  have hint : ∀ z : D.host.K, IsIntegral ℤ (φ z) → IsIntegral ℤ z := fun z hz =>
    (isIntegral_algHom_iff φ.toIntAlgHom hφ).1 hz
  have hmem : ∀ w : Qb, w ∈ KQbar D jE → ∃ z : D.host.K, φ z = w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := (IntermediateField.mem_map _).1 hw
    exact ⟨⟨z, hz⟩, rfl⟩
  have hp0 : (p : Qb) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hπ0 : π ≠ 0 := left_ne_zero_of_mul (hσ ▸ hp0)
  have hσπ : σ π = p / π := by rw [← hσ, mul_div_cancel_left₀ _ hπ0]
  have hσK : σ π ∈ KQbar D jE := hσπ ▸ div_mem (natCast_mem _ p) hπK
  obtain ⟨x, hx⟩ := hmem π hπK
  obtain ⟨y, hy⟩ := hmem (σ π) hσK
  let σZ : Qb →ₐ[ℤ] Qb := σ.toRingHom.toIntAlgHom
  let a : 𝓞 D.host.K := ⟨x, hint x (hx ▸ hπi)⟩
  let b : 𝓞 D.host.K := ⟨y, hint y (hy ▸ hπi.map σZ)⟩

  have hab : a * b = p := by
    apply RingOfIntegers.coe_injective
    apply hφ
    rw [map_mul, map_natCast, map_mul, map_natCast]
    show φ x * φ y = _
    rw [hx, hy, hσ]

  have hdvd : ∀ z : 𝓞 D.host.K,
      IsIntegral ℤ ((φ z - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb)) →
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.K) ∣ z - 1 := by
    intro z hz
    set c : ℕ := D.host.QS * D.host.q * D.host.d
    have hcK : (c : D.host.K) ≠ 0 := by exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
    have hφw : φ (((z : D.host.K) - 1) / c) = (φ z - 1) / c := by
      rw [map_div₀, map_sub, map_one, map_natCast]
    let w : 𝓞 D.host.K := ⟨((z : D.host.K) - 1) / c, hint _ (hφw ▸ hz)⟩
    refine ⟨w, RingOfIntegers.coe_injective ?_⟩
    show (z : D.host.K) - 1 = (c : D.host.K) * (((z : D.host.K) - 1) / c)
    rw [mul_div_cancel₀ _ hcK]
  have hca := hdvd a (by show IsIntegral ℤ ((φ x - 1) / _); rw [hx]; exact hπc)
  have hcb := hdvd b (by
    show IsIntegral ℤ ((φ y - 1) / _)
    have e : σZ ((π - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb)) =
        (σ π - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) := by
      show σ _ = _
      rw [map_div₀, map_sub, map_one, map_natCast]
    rw [hy, ← e]
    exact hπc.map σZ)

  have hpu : ¬ IsUnit (p : 𝓞 D.host.K) := not_isUnit_natCast hpp
  have hunit : ∀ (z : 𝓞 D.host.K), (z : D.host.K) ≠ 0 → IsIntegral ℤ (φ z)⁻¹ → IsUnit z := by
    intro z hz0 hz
    have hi : IsIntegral ℤ ((z : D.host.K)⁻¹) := hint _ (by rw [map_inv₀]; exact hz)
    refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : 𝓞 D.host.K) (RingOfIntegers.coe_injective ?_)
    show (z : D.host.K) * (z : D.host.K)⁻¹ = 1
    exact mul_inv_cancel₀ hz0
  have hinv : ∀ (z : 𝓞 D.host.K), IsUnit z → IsIntegral ℤ (φ z)⁻¹ := by
    intro z hz
    obtain ⟨u, rfl⟩ := hz
    have h1 : (algebraMap (𝓞 D.host.K) D.host.K) ((u⁻¹ : (𝓞 D.host.K)ˣ) : 𝓞 D.host.K) =
        ((algebraMap (𝓞 D.host.K) D.host.K) (u : 𝓞 D.host.K))⁻¹ :=
      map_units_inv (algebraMap (𝓞 D.host.K) D.host.K) u
    have h2 : φ ((algebraMap (𝓞 D.host.K) D.host.K) ((u⁻¹ : (𝓞 D.host.K)ˣ) : 𝓞 D.host.K)) =
        (φ ((u : 𝓞 D.host.K) : D.host.K))⁻¹ := by
      rw [h1, map_inv₀]
    rw [← h2]
    exact (RingOfIntegers.isIntegral_coe _).map φ.toIntAlgHom
  have hx0 : (x : D.host.K) ≠ 0 := fun h0 => hπ0 (by rw [← hx, h0, map_zero])
  have hy0 : (y : D.host.K) ≠ 0 := fun h0 => hp0 (by rw [← hσ, ← hy, h0, map_zero, mul_zero])
  have hu : ¬ IsUnit a := fun ha => hpu (by
    have h1 := (hinv a ha).map σZ
    have h2 : σZ (φ x)⁻¹ = (φ y)⁻¹ := by
      show σ (φ x)⁻¹ = _
      rw [map_inv₀, hx, hy]
    rw [← hab]
    exact ha.mul (hunit b hy0 (h2 ▸ h1)))
  have hu' : ¬ IsUnit b := fun hb => hpu (by
    haveI : Algebra.IsAlgebraic ℚ Qb := by
      unfold Qb; convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
    let τ : Qb ≃ₐ[ℚ] Qb := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
    let τZ : Qb →ₐ[ℤ] Qb := τ.symm.toRingEquiv.toRingHom.toIntAlgHom
    have h1 := (hinv b hb).map τZ
    have h2 : τZ (φ y)⁻¹ = (φ x)⁻¹ := by
      show τ.symm (φ y)⁻¹ = _
      rw [map_inv₀, hy, hx]
      congr 1
      exact τ.symm_apply_apply π
    rw [← hab]
    exact (hunit a hx0 (h2 ▸ h1)).mul hb)

  have hpc : ¬ p ∣ D.host.QS * D.host.q * D.host.d := fun hd => hpu (by
    have h1 : (p : 𝓞 D.host.K) ∣ a - 1 := (Nat.cast_dvd_cast hd).trans hca
    have h2 : (p : 𝓞 D.host.K) ∣ b - 1 := (Nat.cast_dvd_cast hd).trans hcb
    have h3 : (1 : 𝓞 D.host.K) = p - (a * (b - 1) + (a - 1)) := by rw [← hab]; ring
    exact isUnit_of_dvd_one (h3 ▸ dvd_sub dvd_rfl (dvd_add (h2.mul_left _) h1)))
  have hd : ¬ (p : ℤ) ∣ discr M := fun hd => hpc (GlobalTheory.Mem.RaySplit.unr_of_ray hM p hpp hd)
  exact (GlobalTheory.HostSplit.ncard_placesOver M hpp).trans
    (GlobalTheory.Mem.RaySplit.ncard_primesOver_eq hM (GlobalTheory.Mem.RaySplit.isEmpty_real D.host)
      (GlobalTheory.Mem.RaySplit.finrank_K D.host) hpp hd hab hu hu' hca hcb)

end GlobalTheory.ParRay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetric
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Mem.Df

set_option maxHeartbeats 1000000

theorem card_stabilizer_eq_of_smul {G α : Type*} [Group G] [MulAction G α] (g : G) (x : α) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv).symm

private theorem finset_sum_univ_eq_of_equiv {α β M : Type*} [AddCommMonoid M] (i1 : Fintype α) (i2 : Fintype β) (e : α ≃ β)
    (f : α → M) (g : β → M) (h : ∀ x, f x = g (e x)) :
    @Finset.sum α M _ (@Finset.univ α i1) f = @Finset.sum β M _ (@Finset.univ β i2) g :=
  @Fintype.sum_equiv α β M i1 i2 _ e f g h

theorem ipMt_eq_cSum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (F G : (I.per l u a).Mt) (F' G' : MtCx I a), SameForm I l u a F' F → SameForm I l u a G' G → I.ipMt l u a F G = cSum I hX a F' G' := by
  intro B X I hOk hP l hX Z u a F G F' G' hF hG
  rw [GlobalTheory.Mem.Col2.IpMt.ipMt_sum I hOk hP l Z u a F G]
  have hd : Disjoint (B.primes X).vGs (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K)) :=
    (GlobalTheory.TopStep.tilOk_of_avoid (mu := I.tup a) l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.2
  have hs : (I.perIn u a).sgT = B.wts.sgTrue := by
    funext τ
    rfl
  rw [hs, GlobalTheory.Mem.Df.cSum_apply]
  refine finset_sum_univ_eq_of_equiv _ _ (GlobalTheory.PeriodOnStep.clEquiv (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd) _ _ (fun c => ?_)
  have hFc := hF ((stepX I.Ch I.sel (I.tup a) I.Ps).rep c)
  have hGc := hG ((stepX I.Ch I.sel (I.tup a) I.Ps).rep c)
  have hcls : (rowS I a).cls ((rowS I a).outSec.rep ((GlobalTheory.PeriodOnStep.clEquiv (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd) c)) =
      (rowS I a).cls (GlobalTheory.PeriodOnStep.rowPt (X := B.fields) (Pr := B.primes X) (R := B.R) I.Ch I.sel (I.tup a) I.Ps c) :=
    (rowS I a).outSec.spec _
  obtain ⟨g, hg⟩ := ((rowS I a).cls_eq_iff _ _).1 hcls
  have hcard := GlobalTheory.PeriodOnStep.card_stab (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd c
  have hpair := _root_.GlobalTheory.Mem.Df.pairB_conj_cls_eq I hX a F' G' _ _ hcls
  unfold cTerm
  rw [hpair, ← hg, @card_stabilizer_eq_of_smul (rowS I a).G (rowS I a).D _ (rowS I a).actD g _, ← hcard]
  exact congrArg₂ (fun x y => (((Nat.card ((stepX I.Ch I.sel (I.tup a) I.Ps).Stab c) : ℕ) : ℂ))⁻¹ *
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) x) y) hFc hGc

end GlobalTheory.Mem.Df

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjective
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.TameKummerInertia

theorem unram_of_fixed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (L : IntermediateField E Ω) [FiniteDimensional E L] [IsGalois E L] [NumberField L] (K : IntermediateField E L) [NumberField K] (Q : Ideal (𝓞 L)) [Q.IsPrime], (∀ x : 𝓞 L, x ∈ Q ↔ A.valuation (((x : L) : Ω)) < 1) → (∀ σ ∈ Ine (F := E) A, ∀ y : K, σ (((y : L) : Ω)) = ((y : L) : Ω)) → (Q.under (𝓞 K)).ramificationIdx (𝓞 E) = 1 := by
  intro E Ω _ _ _ _ _ A L _ _ _ K _ Q _ hQ hfix
  rw [GlobalTheory.UnramCompositum.ramificationIdx_eq_one_iff_fix E K L Q]
  intro τ hτ y
  have hint : ∀ a : 𝓞 L, A.valuation (algebraMap L Ω (a : L)) ≤ 1 := fun a =>
    GlobalTheory.CMRam.val_int_le (algebraMap L Ω) A a
  have hsm : ∀ a : 𝓞 L, ((τ • a : 𝓞 L) : L) = τ (a : L) := fun a => rfl
  have hτ' : ∀ a : 𝓞 L, A.valuation (algebraMap L Ω (τ (a : L)) - algebraMap L Ω (a : L)) < 1 := by
    intro a
    have := (hQ _).1 (hτ a)
    simpa [hsm] using this
  have hlift : ∀ x : L, A.valuation (algebraMap L Ω x) ≤ 1 →
      A.valuation (algebraMap L Ω (τ x) - algebraMap L Ω x) < 1 := by
    intro x hx
    obtain ⟨s, t, hs, e⟩ := GlobalTheory.CMRam.exists_den_field (algebraMap L Ω) A (x := x) hx
    have hτs : A.valuation (algebraMap L Ω (τ (s : L))) = 1 := by
      refine le_antisymm ?_ ?_
      · have := hint (τ • s); rwa [hsm] at this
      · by_contra hlt
        push Not at hlt
        have h2 : A.valuation (algebraMap L Ω (s : L)) < 1 := by
          have e2 : algebraMap L Ω (s : L) = algebraMap L Ω (τ (s : L)) - (algebraMap L Ω (τ (s : L)) - algebraMap L Ω (s : L)) := by ring
          rw [e2]; exact Valuation.map_sub_lt _ hlt (hτ' s)
        rw [hs] at h2; exact lt_irrefl _ h2
    have he' : τ (s : L) * τ x = τ (t : L) := by rw [← map_mul, e]
    have key : algebraMap L Ω (τ (s : L)) * (algebraMap L Ω (τ x) - algebraMap L Ω x) =
        (algebraMap L Ω (τ (t : L)) - algebraMap L Ω (t : L)) + algebraMap L Ω x * (algebraMap L Ω (s : L) - algebraMap L Ω (τ (s : L))) := by
      rw [← he', ← e]; simp only [map_mul]; ring
    have hv : A.valuation (algebraMap L Ω (τ (s : L)) * (algebraMap L Ω (τ x) - algebraMap L Ω x)) < 1 := by
      rw [key]
      refine Valuation.map_add_lt _ (hτ' t) ?_
      rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation (algebraMap L Ω x) * A.valuation (algebraMap L Ω (τ (s : L)) - algebraMap L Ω (s : L))
          ≤ 1 * A.valuation (algebraMap L Ω (τ (s : L)) - algebraMap L Ω (s : L)) := mul_le_mul_left hx _
        _ < 1 := by rw [one_mul]; exact hτ' s
    rwa [Valuation.map_mul, hτs, one_mul] at hv
  obtain ⟨σ, hσ, hσx⟩ := GlobalTheory.InertiaLift.exists_mem_Ine_lift A L τ hlift
  apply Subtype.ext
  have h1 := hσx (algebraMap K L y)
  have h2 := hfix σ hσ y
  exact (h1.symm.trans h2 : _)

theorem index_one_root : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (P : Ideal (𝓞 K)) [P.IsPrime], P.under (𝓞 E) = v.asIdeal → P.ramificationIdx (𝓞 E) = 1 → ∀ (g : ℕ), ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (k : ℕ) (Z : K), Z ^ k = ((g : ℕ) : K) → k ≤ 1 := by
  intro E K _ _ _ _ _ v P _ hPv he g hgv hgv2 k Z hZ
  by_contra hk
  push Not at hk
  haveI : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  have he' : Ideal.ramificationIdx' v.asIdeal P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal P v.ne_bot]; exact he
  have hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≤ P :=
    Ideal.map_le_iff_le_comap.2 (le_of_eq hPv.symm)
  have hnot : ¬ Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≤ P ^ 2 := fun h =>
    (Ideal.ramificationIdx'_ne_one_iff hmap).2 h he'
  have hZi : IsIntegral ℤ Z := by
    refine IsIntegral.of_pow (n := k) (by omega) ?_
    rw [hZ, ← map_natCast (algebraMap ℤ K) g]
    exact isIntegral_algebraMap
  set z : 𝓞 K := ⟨Z, hZi⟩ with hzdef
  have hz : z ^ k = ((g : ℕ) : 𝓞 K) := by
    apply NumberField.RingOfIntegers.ext
    simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_natCast]
    exact hZ
  have hgP : ((g : ℕ) : 𝓞 K) ∈ P := by
    have h0 : ((g : ℕ) : 𝓞 E) ∈ P.under (𝓞 E) := hPv ▸ hgv
    rw [Ideal.under, Ideal.mem_comap, map_natCast] at h0
    exact h0
  have hzP : z ∈ P := Ideal.IsPrime.mem_of_pow_mem ‹_› k (hz ▸ hgP)
  have hgP2 : ((g : ℕ) : 𝓞 K) ∈ P ^ 2 := by
    rw [← hz, show k = 2 + (k - 2) by omega, pow_add]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hzP 2)
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {((g : ℕ) : 𝓞 E)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hgv)
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle; apply hgv2
    have : Ideal.span {((g : ℕ) : 𝓞 E)} ≤ v.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self _)
  obtain ⟨j, hjJ, hjv⟩ := Set.not_subset.1 hJv
  have hjP : algebraMap (𝓞 E) (𝓞 K) j ∉ P := by
    intro h; apply hjv; rw [← hPv]; exact h
  haveI hPmax : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) P
    (by rw [hPv]; exact v.isMaximal)
  have hrad : (P ^ 2).radical = P := by rw [Ideal.radical_pow _ two_ne_zero, hPmax.isPrime.radical]
  have hprim : (P ^ 2).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hPmax)
  apply hnot
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hxj : x * j ∈ Ideal.span {((g : ℕ) : 𝓞 E)} := by rw [hJ]; exact Ideal.mul_mem_mul hx hjJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hxj
  have h1 : algebraMap (𝓞 E) (𝓞 K) j * algebraMap (𝓞 E) (𝓞 K) x ∈ P ^ 2 := by
    rw [← map_mul, mul_comm, ← hc, map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ hgP2
  rcases hprim.mem_or_mem h1 with h | h
  · exact h
  · exfalso; rw [Submodule.colon_univ, hrad] at h; exact hjP h

theorem tame_kummer_surj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (m : ℕ), 0 < m → ¬ g ∣ m → ∀ Y μ : Ω, Y ^ m = ((g : ℕ) : Ω) → μ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ Y = μ * Y := by
  intro E Ω _ _ _ _ _ A v hA g _ hgv hgv2 m hm hgm Y μ hY hμ
  have hgp : g.Prime := Fact.out
  have hg := GlobalTheory.TameCoupledEx.val_g_lt A v hA hgv
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : NeZero m := ⟨hm.ne'⟩
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  have hY0 : Y ≠ 0 := GlobalTheory.TameCoupledEx.ne_zero_of_pow_eq hgp hm hY
  have hpow : ∀ σ : G E Ω, (σ Y / Y) ^ m = 1 := fun σ => tameQuot_pow σ hg0 hY
  have hne : ∀ σ : G E Ω, σ Y / Y ≠ 0 := fun σ => div_ne_zero (by simpa using hY0) hY0
  let χ : Ine (F := E) A →* rootsOfUnity m Ω :=
    { toFun := fun σ => ⟨Units.mk0 (σ.1 Y / Y) (hne σ.1), by
        rw [mem_rootsOfUnity]; ext; simp [hpow]⟩
      map_one' := by ext; simp [hY0]
      map_mul' := fun σ τ => by
        ext
        simp only [Subgroup.coe_mul, Units.val_mk0, Subgroup.coe_mul, Units.val_mul]
        exact GlobalTheory.TameCoupledEx.ratio_mul hgp hg σ.2 τ.1 hm hgm hY }
  have hχ : ∀ σ, (((χ σ : rootsOfUnity m Ω) : Ωˣ) : Ω) = σ.1 Y / Y := fun σ => rfl
  obtain ⟨⟨c, σ0, hσ0⟩, hc⟩ := IsCyclic.exists_generator (α := χ.range)
  set d := orderOf c with hd
  have hcm : c ^ m = 1 := by
    ext; simpa [← hσ0, hχ] using hpow σ0.1
  have hdm : d ∣ m := orderOf_dvd_of_pow_eq_one hcm
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm
  have hall : ∀ σ : G E Ω, σ ∈ Ine (F := E) A → (σ Y / Y) ^ d = 1 := by
    intro σ hσ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hc ⟨χ ⟨σ, hσ⟩, ⟨σ, hσ⟩, rfl⟩)
    have h1 : (χ ⟨σ, hσ⟩) ^ d = 1 := by
      have := congrArg Subtype.val hj
      simp only [Subgroup.coe_zpow] at this
      rw [← this, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd, pow_orderOf_eq_one, one_zpow]
    have h2 := congrArg (fun u : rootsOfUnity m Ω => ((u : Ωˣ) : Ω)) h1
    simpa [hχ] using h2
  set Z := Y ^ d with hZ
  have hZfix : ∀ σ : G E Ω, σ ∈ Ine (F := E) A → σ Z = Z := by
    intro σ hσ
    have e : σ Y = (σ Y / Y) * Y := by field_simp
    rw [hZ, map_pow, e, mul_pow, hall σ hσ, one_mul]
  set n := m / d with hn
  have hnd : d * n = m := Nat.mul_div_cancel' hdm
  have hZn : Z ^ n = ((g : ℕ) : Ω) := by rw [hZ, ← pow_mul, hnd, hY]
  have hn1 : n ≤ 1 := by
    have hZi : IsIntegral E Z := Algebra.IsIntegral.isIntegral Z
    haveI : FiniteDimensional E (IntermediateField.adjoin E {Z}) := IntermediateField.adjoin.finiteDimensional hZi
    set L := IntermediateField.normalClosure E (IntermediateField.adjoin E {Z}) Ω with hLdef
    haveI : NumberField L := NumberField.of_module_finite E L
    have hZL : Z ∈ L := IntermediateField.le_normalClosure _ (IntermediateField.mem_adjoin_simple_self E Z)
    set Z' : L := ⟨Z, hZL⟩ with hZ'
    set K : IntermediateField E L := IntermediateField.adjoin E {Z'} with hK
    haveI : NumberField K := NumberField.of_module_finite E K
    let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring
      (fun x => ReciprocityTheory.Gal.mem_of_isIntegral_int A ((x.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ L Ω))))
    set Q : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f with hQ
    haveI : Q.IsPrime := Ideal.comap_isPrime f _
    have hQmem : ∀ x : 𝓞 L, x ∈ Q ↔ A.valuation (((x : L) : Ω)) < 1 := fun x =>
      Ideal.mem_comap.trans (ValuationSubring.valuation_lt_one_iff A (f x))
    have hfixK : ∀ σ ∈ Ine (F := E) A, ∀ y : K, σ (((y : L) : Ω)) = ((y : L) : Ω) := by
      intro σ hσ y
      have hle : K.toSubalgebra ≤ AlgHom.equalizer ((σ : Ω →ₐ[E] Ω).comp L.val) L.val := by
        rw [hK, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic Z')]
        refine Algebra.adjoin_le ?_
        rintro _ rfl
        exact hZfix σ hσ
      exact hle y.2
    have e1 := unram_of_fixed E Ω A L K Q hQmem hfixK
    have hunder : (Q.under (𝓞 K)).under (𝓞 E) = v.asIdeal := by
      ext x
      rw [Ideal.under_under, Ideal.mem_comap, hQmem, ← hA x]
      rfl
    set Z'' : K := ⟨Z', IntermediateField.mem_adjoin_simple_self E Z'⟩ with hZ''
    have hZ''n : Z'' ^ n = ((g : ℕ) : K) := by
      apply Subtype.ext; apply Subtype.ext
      simpa using hZn
    exact index_one_root E K v (Q.under (𝓞 K)) hunder e1 g hgv hgv2 n Z'' hZ''n
  have hdm' : d = m := by
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro h; rw [h, mul_zero] at hnd; exact hm.ne' hnd.symm)
    have : n = 1 := le_antisymm hn1 hn0
    rw [this, mul_one] at hnd; exact hnd
  have hprim : IsPrimitiveRoot (σ0.1 Y / Y) m := by
    have h1 : orderOf (σ0.1 Y / Y) = m := by
      rw [← hχ, orderOf_units, Subgroup.orderOf_coe, hσ0, ← hd, hdm']
    rw [← h1]; exact IsPrimitiveRoot.orderOf _
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hμ
  refine ⟨σ0.1 ^ i, pow_mem σ0.2 i, ?_⟩
  have := GlobalTheory.TameCoupledEx.ratio_pow hgp hg σ0.2 hm hgm hY i
  rw [hi] at this
  field_simp at this
  rw [this, mul_comm]

end GlobalTheory.TameKummerInertia
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeVISupIndep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.MtIndep

section rep
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isoRep_trans {W₁ W₂ W₃ : Type} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    [AddCommGroup W₃] [Module ℂ W₃] {S₁ : Submodule ℂ (GAf L n → W₁)} {S₂ : Submodule ℂ (GAf L n → W₂)}
    {S₃ : Submodule ℂ (GAf L n → W₃)} (h₁ : NG.IsoRep S₁ S₂) (h₂ : NG.IsoRep S₂ S₃) : NG.IsoRep S₁ S₃ := by
  obtain ⟨T, hT⟩ := h₁
  obtain ⟨U, hU⟩ := h₂
  exact ⟨T.trans U, fun h f f' e => hU h (T f) (T f') (hT h f f' e)⟩

theorem isoRep_symm {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ (GQ L n) W} {S₁ : Submodule ℂ (GAf L n → W)} {S₂ : Submodule ℂ (GAf L n → W')}
    (hs : NG.IsSubrep ρ S₁) (h : NG.IsoRep S₁ S₂) : NG.IsoRep S₂ S₁ := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun h g g' e => ?_⟩
  have hm : NG.rt L n h ((T.symm g : S₁) : GAf L n → W) ∈ S₁ := hs.stable h _ (T.symm g).2
  have key := hT h (T.symm g) ⟨_, hm⟩ rfl
  rw [LinearEquiv.apply_symm_apply] at key
  have hg : T ⟨_, hm⟩ = g' := Subtype.ext (key.trans e.symm)
  rw [← hg, LinearEquiv.symm_apply_apply]

theorem isoTyp_eq {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GQ L n) W}
    {S₁ S₂ : Submodule ℂ (GAf L n → W)} (hs : NG.IsSubrep ρ S₁) (h : NG.IsoRep S₁ S₂) :
    NG.isoTyp ρ S₁ = NG.isoTyp ρ S₂ := by
  unfold NG.isoTyp
  congr 1
  ext S'
  simp only [Set.mem_setOf_eq]
  exact and_congr_right fun _ => ⟨fun h' => isoRep_trans (isoRep_symm hs h) h', fun h' => isoRep_trans h h'⟩

end rep

section loc
variable {D : D7}

def BCd (X : LocNd (lay0 D)) (Y : LocAut X) (Pa : List (Part Y.naut.CG)) (loc : ∀ w, Y.naut.LP w)
    (sat : PlE D.host → Multiset ℂ) (inf : (D.host.E →+* ℂ) → Multiset ℂ) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ Y.naut.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, Y.naut.CG a), p.d)).Nodup ∧
  rankIso X.nd Y.naut Pa = D.R.nV ∧
  (∀ w, IsSplitPl D.host w → isoLoc X.nd Y.naut Pa w = loc w) ∧
  (∀ w, ¬ IsSplitPl D.host w → Y.naut.unr (isoLoc X.nd Y.naut Pa w) ∧
    Y.naut.frobEig (isoLoc X.nd Y.naut Pa w) = ubc D.R.nV (sat w)) ∧
  ∀ τ, isoInf X.nd Y.naut Pa τ = inf τ

def Good (X : LocNd (lay0 D)) (Y : LocAut X) (σ' : D.ntypes.Par) (c : Y.naut.CG 1) (j : ℕ) (u : D.nbc.AU j) : Prop :=
  ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧
    BCd X Y (twistIso X.nd Y.naut (Sig ++ [⟨1, c, D.R.t⟩]) Y.naut.etaTinv) (fun w => D.nbc.locAU j u w)
      (D.nbc.satAU j u) (D.nbc.infW j (D.nbc.wtAU j u))

end loc

end GlobalTheory.HeightCounting.MtIndep

namespace GlobalTheory.HeightCounting.MtIndep

section loc2
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {X : LocNd (lay0 D)}
  {iq : ∀ i : X.nd.Loc, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)} {Y : LocAut X} {Cb : LocBC Y}

end loc2

end GlobalTheory.HeightCounting.MtIndep
end
end

