module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemClosureMulVOfFinrankEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

theorem semilinear_coord_fixed {F D ι : Type*} [Field F] [AddCommGroup D] [Module F D] [Fintype ι]
    {b : ι → D} (hb : LinearIndependent F b) (σ : F → F) (T : D →+ D)
    (hT : ∀ c x, T (c • x) = σ c • T x) (hTb : ∀ i, T (b i) = b i) (c : ι → F)
    (h : T (∑ i, c i • b i) = ∑ i, c i • b i) (i : ι) : σ (c i) = c i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h
  simp only [hT, hTb] at h
  exact Fintype.linearIndependent_iffₛ.mp hb _ _ h i

variable {l : ℕ} [Fact l.Prime]

theorem galois_mem_Kur (g : GQ l) (c : ↥(MaximalUnramifiedExtension l)) : g (c : Om l) ∈ MaximalUnramifiedExtension l := by
  obtain ⟨c, hc⟩ := c
  change g c ∈ MaximalUnramifiedExtension l
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, h0, hm, hx⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨m, h0, hm, by rw [← map_pow, hx, map_one]⟩
  | algebraMap x => rw [g.commutes]; exact (MaximalUnramifiedExtension l).algebraMap_mem x
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact (MaximalUnramifiedExtension l).add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact (MaximalUnramifiedExtension l).inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact (MaximalUnramifiedExtension l).mul_mem hx hy

theorem mem_of_GK_fixed {K : FinExt l} {x : Om l} (hx : ∀ g : ↥(GK K), (g : GQ l) x = x) : x ∈ K.1 := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
  exact fun g hg => hx ⟨g, hg⟩

theorem mulV_padic_smul (P : LocPrime l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (q : ℚ_[l]) (c : ↥(MaximalUnramifiedExtension l)) (x : V ⊗[ℚ_[l]] Bst P) :
    mulV P LL V (q • c) x = q • mulV P LL V c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [mulV_tmul, mulV_tmul, ← tmul_smul, Algebra.smul_def q c, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_assoc, ← Algebra.smul_def]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem mem_closure_mulV_of_finrank_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsPst P ρ → ∀ S : Submodule ↥LL.1 (V ⊗[ℚ_[l]] Bst P), S ≤ Dst P ρ → (∀ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 → ∀ x ∈ S, mulV P ↥LL.1 V c x ∈ S) → finrank ↥LL.1 ↥S = finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V → ∀ x ∈ Dpst P ρ, x ∈ AddSubgroup.closure {y | ∃ (c : ↥(MaximalUnramifiedExtension l)) (s : V ⊗[ℚ_[l]] Bst P), s ∈ S ∧ y = mulV P ↥LL.1 V c s} := by
  intro l _ P K LL V _ _ _ _ _ ρ hV S hS _ hrk x hx
  haveI := LL.2
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  obtain ⟨hfin, hd⟩ := (isPst_iff P ρ).mp hV
  let val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P :=
    (Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom
  have hSD : S ≤ Dpst P ρ := fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp (hS hs) g⟩
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ S}
  haveI : Finite ↥b := hli.finite
  letI : Fintype ↥b := Fintype.ofFinite _
  have hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l),
      ∑ i, c i • (i : DpstUr P ρ) = y := fun y hy => by
    rw [← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]; exact hy
  let inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)
  let f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    { toFun := fun c => ∑ i, mulV P ↥LL.1 V (inc (c i)) (val i)
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun q c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }
  have hle : S.restrictScalars ℚ_[l] ≤ LinearMap.range f := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)
    have hfix : ∀ i, (c i : Om l) ∈ K.1 := fun i => mem_of_GK_fixed fun g => by
      have := semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩)
        (actD P ρ g).toAddMonoidHom
        (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y)
        (fun j => Subtype.ext ((mem_Dst P ρ).mp (hS (hbS j.2)) g)) c
        (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp (hS hs) g)) i
      exact congrArg Subtype.val this
    refine ⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩
    have := congrArg val hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    exact this
  have h1 : finrank ℚ_[l] ↥(S.restrictScalars ℚ_[l]) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K) := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    simp [Module.finrank_pi_fintype]
  have h2 : finrank ℚ_[l] ↥(S.restrictScalars ℚ_[l]) = finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K) := by
    change finrank ℚ_[l] ↥S = _
    have : Module.Free ↥LL.1 ↥S := Module.Free.of_divisionRing _ _
    rw [← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 ↥S, hrk, ← Module.finrank_mul_finrank ℚ_[l] ↥LL.1 V]
    ring
  have h3 : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ Fintype.card ↥b := by
    rw [hd]
    exact Nat.le_of_mul_le_mul_right (h2 ▸ h1) Module.finrank_pos
  have htop := hli.span_eq_top_of_card_eq_finrank' (le_antisymm hli.fintype_card_le_finrank h3)
  rw [Subtype.range_coe] at htop
  obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨x, hx⟩) (htop ▸ Submodule.mem_top)
  have h4 := congrArg val hc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h4
  rw [← show _ = x from h4]
  exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨c i, val i, hbS i.2, rfl⟩

end GlobalTheory.Pst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct Pointwise

namespace GlobalTheory.HostSplit

theorem jacobiSym_neg_eq_one {r p : ℕ} (hr : r % 2 = 1) (h4 : p % 4 = 1) (h1 : p % r = 1) :
    jacobiSym (-(r : ℤ)) p = 1 := by
  have hgo : Odd p := Nat.odd_iff.mpr (by omega)
  have hdo : Odd r := Nat.odd_iff.mpr hr
  rw [jacobiSym.neg _ hgo, ZMod.χ₄_nat_one_mod_four h4, one_mul,
    jacobiSym.quadratic_reciprocity_one_mod_four' hdo h4, jacobiSym.mod_left]
  have h2 : ((p : ℤ) % (r : ℤ)) = 1 := by
    rw [← Int.natCast_mod, h1]
    rfl
  rw [h2, jacobiSym.one_left]

theorem ncard_placesOver (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    (placesOver E p).ncard = (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have himg : HeightOneSpectrum.asIdeal '' placesOver E p =
      Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hPp := v.isPrime
      refine ⟨hPp, ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_⟩⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ v.asIdeal
      rw [map_natCast]
      exact hv
    · rintro ⟨h1, h2⟩
      refine ⟨⟨P, h1, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩, ?_, rfl⟩
      have h3 : (p : ℤ) ∈ P.under ℤ := by
        rw [← Ideal.over_def P (Ideal.span {(p : ℤ)})]
        exact Ideal.mem_span_singleton_self _
      have h4 : algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ P := h3
      rw [map_natCast] at h4
      exact h4
  rw [← himg, Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)]

theorem ncard_primesOver_of_stabilizer (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (h : ∀ σ : E ≃ₐ[ℚ] E, σ ∈ MulAction.stabilizer (E ≃ₐ[ℚ] E) P → σ = 1) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  have : IsGaloisGroup (E ≃ₐ[ℚ] E) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hr : Set.range (fun σ : E ≃ₐ[ℚ] E => σ • P) = Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨inferInstance, inferInstance⟩
    · rintro ⟨hQ1, hQ2⟩
      exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have hinj : Function.Injective (fun σ : E ≃ₐ[ℚ] E => σ • P) := by
    intro σ τ hστ
    have h1 : τ⁻¹ * σ = 1 := by
      apply h
      rw [MulAction.mem_stabilizer_iff, mul_smul]
      have h2 : σ • P = τ • P := hστ
      rw [h2, inv_smul_smul]
    exact (inv_mul_eq_one.mp h1).symm
  rw [← hr, Set.ncard_range_of_injective hinj, IsGalois.card_aut_eq_finrank]

theorem split_of_one_mod : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime → p % (H.QS * H.q * H.d) = 1 →
    (placesOver H.E p).ncard = Module.finrank ℚ H.E ∧ H.cls p = PrimeClass.splitK := by
  intro R H p hp hc
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hmod : ∀ m : ℕ, 1 < m → m ∣ H.QS * H.q * H.d → p % m = 1 := by
    intro m hm hdv
    rw [← Nat.mod_mod_of_dvd p hdv, hc]
    exact Nat.mod_eq_of_lt hm
  have h4Q : 4 ∣ H.QS := (show (2 : ℕ) ^ 2 ∣ 2 ^ (R.e + 2) from pow_dvd_pow 2 (by omega)).trans H.tower_dvd
  have h4 : p % 4 = 1 := hmod 4 (by norm_num) ((h4Q.mul_right _).mul_right _)
  have hd : p % H.d = 1 := hmod _ (by omega) (dvd_mul_left _ _)
  have hnd : ∀ m : ℕ, m ∣ H.QS * H.q * H.d → ¬ p ∣ m := by
    intro m hm hpm
    have h := hmod p hp.one_lt (hpm.trans hm)
    rw [Nat.mod_self] at h
    omega
  have hN : ¬ p ∣ H.condN := hnd _ dvd_rfl
  have hp2 : p ∉ H.small := fun h =>
    hnd H.QS (((dvd_refl _).mul_right _).mul_right _) (Nat.dvd_of_mem_primeFactors h)
  have hpq : p ≠ H.q := fun h => hnd H.q ((dvd_mul_left _ _).mul_right _) (h ▸ dvd_rfl)
  have hpd : p ≠ H.d := fun h => hnd H.d (dvd_mul_left _ _) (h ▸ dvd_rfl)
  have jd := jacobiSym_neg_eq_one (r := H.d) (by omega) h4 hd
  refine ⟨?_, ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hG : IsGalois ℚ H.E := H.galois
    have := Formalism.FrobeniusOrbits.SplitK.span_prime p
    obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 H.E)))
    obtain ⟨-, hF, -, hI⟩ := H.der.frob p hN P
    have h1 : IsArithFrobAt ℤ (1 : H.E ≃ₐ[ℚ] H.E) P := by
      refine (hF 1 1 ?_).2 (by rw [map_one, map_one])
      rw [← ZMod.natCast_mod p, show p % H.condN = 1 from hc]
      simp
    rw [ncard_placesOver H.E hp]
    refine ncard_primesOver_of_stabilizer H.E p P fun σ hσ => ?_
    obtain ⟨k, ρ, hρ, rfl⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul p P 1 σ h1 hσ
    rw [(hI ρ).1 hρ, one_pow, mul_one]
  · unfold Host.cls primeClass
    rw [if_neg hp2, if_neg hpq, if_neg hpd, if_pos jd]

end GlobalTheory.HostSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedTheta

variable {l : ℕ} [Fact l.Prime]


open Classical in
def thetaExt (x : Per.BdR l) : ℂ_[l] :=
  if h : ∃ y : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) y = x then Per.θD l h.choose else 0

theorem thetaExt_alg (y : Per.BdRp l) :
    thetaExt (algebraMap (Per.BdRp l) (Per.BdR l) y) = Per.θD l y := by
  have h : ∃ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) z =
      algebraMap (Per.BdRp l) (Per.BdR l) y := ⟨y, rfl⟩
  rw [thetaExt, dite_eq_left h, (BdRField.bdR_isField l).2.1 h.choose_spec]

theorem exists_of_mem_FilD_zero {x : Per.BdR l} (hx : x ∈ Per.FilD l 0) :
    ∃ y : Per.BdRp l, x = algebraMap (Per.BdRp l) (Per.BdR l) y := by
  obtain ⟨e, he⟩ := FilLaws.exists_isEps l
  obtain ⟨y, hy⟩ := (mem_FilD_iff_xi_pow l e he 0 x).1 hx
  exact ⟨y, by simpa using hy⟩

theorem actC_eq {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (c : ℂ_[l]) :
    AI.actC g c = Per.σC g c := by
  have h1 : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  have h2 : Continuous (Per.σC g) :=
    (AddMonoidHomClass.isometry_of_norm (Per.σC g) (GlobalTheory.RingBasics.norm_σC g)).continuous
  induction c using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq h1 h2
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem norm_untilt_sub (x : Per.Fl l) (y : Per.OC l)
    (h : PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) y) :
    ‖((x.untilt : Per.OC l) : ℂ_[l]) - (y : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  rw [← PreTilt.mk_untilt_eq_coeff_zero, Ideal.Quotient.eq] at h
  have h1 := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (x.untilt - y)).1 (by rwa [pow_one])
  rw [pow_one] at h1
  exact h1

theorem nonempty_thetaL : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → Nonempty (Formalism.MainNotions.LocalSituation.ThetaL P AI) := by
  intro l _ P AI T
  have hex : ∀ x ∈ (P.PD (MainNotions.LocalSituation.botExt l)).Fil 0,
      ∃ y : Per.BdRp l, T.eD x = algebraMap (Per.BdRp l) (Per.BdR l) y :=
    fun x hx => exists_of_mem_FilD_zero ((T.fil _ _ _).1 hx)
  have hU := TiedUnif.tied_uniformiser l P AI T
  refine ⟨{
    θ := fun x => thetaExt (T.eD x)
    θ_one := ?_
    θ_add := fun x hx y hy => ?_
    θ_mul := fun x hx y hy => ?_
    θ_onto := fun c => ?_
    θ_ker := fun x hx => ?_
    θ_act := fun g x hx => ?_
    θ_Om := fun x => ?_
    θ_int := fun a => ?_
    θ_teich := fun x y h => ?_
    fil_succ_iff_mul_t := hU.2.2 _
    t_μ := hU.1 _ }⟩
  · rw [map_one, ← map_one (algebraMap (Per.BdRp l) (Per.BdR l)), thetaExt_alg, map_one]
  · obtain ⟨u, hu⟩ := hex x hx
    obtain ⟨v, hv⟩ := hex y hy
    rw [map_add (f := _), hu, hv, ← map_add (f := _), thetaExt_alg, thetaExt_alg, thetaExt_alg, map_add (f := _)]
  · obtain ⟨u, hu⟩ := hex x hx
    obtain ⟨v, hv⟩ := hex y hy
    rw [map_mul, hu, hv, ← map_mul, thetaExt_alg, thetaExt_alg, thetaExt_alg, map_mul]
  · obtain ⟨y, rfl⟩ := (thetaD_props l).1 c
    refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) y), ?_, ?_⟩
    · rw [T.fil, RingEquiv.apply_symm_apply]
      exact TiedUnif.alg_mem_FilD_zero y
    · rw [RingEquiv.apply_symm_apply, thetaExt_alg]
  · obtain ⟨u, hu⟩ := hex x hx
    rw [T.fil, hu, thetaExt_alg, (thetaD_props l).2.1]
    exact ((filD_laws l).2.2.2.2.2.2 1 u).symm
  · obtain ⟨u, hu⟩ := hex x hx
    rw [T.actD, hu, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1, thetaExt_alg, thetaExt_alg,
      (thetaD_props l).2.2.2.2, actC_eq]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    rw [hy, thetaExt_alg, hθ]
  · rw [TiedUnif.eD_ιA T, thetaExt_alg, (thetaD_props l).2.2.2.1]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2
  · rw [TiedUnif.eD_ιA T, thetaExt_alg, (thetaD_props l).2.2.2.1,
      WittVector.fontaineTheta_teichmuller]
    exact norm_untilt_sub x y h

end GlobalTheory.MemLoc.TiedTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenKerCharWildEqOneOfPowEqOne
section
open NumberField IsDedekindDomain

namespace GlobalTheory.WildOpenKernel

theorem eq_one_of_wild_prime {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M)
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P)
    (hop : IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) (l : ℕ) (hl : l.Prime)
    (hlv : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal) (σ : Formalism.ConjugateSelfDual.G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hσl : φ σ ^ l = 1) : φ σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (by simp))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ n ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ n)
      (GlobalTheory.WildInertiaChar.wild_pow A σ hσ n) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : φ σ ^ n = 1 := by
    have h2 : σ ^ n ∈ φ.ker := hsub hτ
    rw [MonoidHom.mem_ker, map_pow] at h2
    exact h2
  have hc : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hn
  have := (pow_gcd_eq_one (a := φ σ) (m := l) (n := n)).mpr ⟨hσl, h1⟩
  rwa [hc, pow_one] at this

theorem eq_one_of_wild : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (m : ℕ),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → (∃ N : ℕ, φ τ ^ (m ^ N) = 1) → φ τ = 1 := by
  intro E Ω _ _ _ _ _ M _ φ P A m hA hop hm τ hτ ⟨N, hN⟩
  by_contra hne
  have hd : orderOf (φ τ) ∣ m ^ N := orderOf_dvd_of_pow_eq_one hN
  have hne1 : orderOf (φ τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
  have hlm : l ∣ m := hl.dvd_of_dvd_pow (dvd_trans ⟨k, hk⟩ hd)
  have hlv : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    intro h
    apply hm
    obtain ⟨c, hc⟩ := hlm
    rw [hc]
    push_cast
    exact Ideal.mul_mem_right _ _ h
  have h1 : φ (τ ^ k) = 1 := by
    refine eq_one_of_wild_prime φ P A hA hop l hl hlv _
      (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
    rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  rw [map_pow] at h1
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have ho : orderOf (φ τ) ≠ 0 := fun h =>
    pow_ne_zero N hm0 (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact ho (by simpa using hk)
  have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
  rw [hk] at h3
  have := hl.two_le
  have := Nat.pos_of_ne_zero hk0
  nlinarith

end GlobalTheory.WildOpenKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmoduleEqSpanOfPowEqSpanPow
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped nonZeroDivisors

namespace GlobalTheory

theorem fractionalIdeal_eq_of_count_eq {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

theorem submodule_eq_span_of_pow_eq_span_pow :
    ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K) (β : K) (h : ℕ),
      0 < h → β ≠ 0 → I.FG → I ^ h = Submodule.span (𝓞 K) {β ^ h} →
      I = Submodule.span (𝓞 K) {β} := by
  intro K _ _ I β h hh hβ hfg hpow
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg hfg⟩
  have hJI : (J : Submodule (𝓞 K) K) = I := rfl
  have hB : FractionalIdeal.spanSingleton (𝓞 K)⁰ β ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ
  have hp : J ^ h = FractionalIdeal.spanSingleton (𝓞 K)⁰ β ^ h := by
    rw [FractionalIdeal.spanSingleton_pow]
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_pow, FractionalIdeal.coe_spanSingleton, hJI, hpow]
  have hJ : J ≠ 0 := by
    intro h0
    rw [h0, zero_pow hh.ne'] at hp
    exact pow_ne_zero h hB hp.symm
  have hJB : J = FractionalIdeal.spanSingleton (𝓞 K)⁰ β := by
    refine fractionalIdeal_eq_of_count_eq hJ hB fun v => ?_
    have := congrArg (FractionalIdeal.count K v) hp
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at this
    exact mul_left_cancel₀ (by exact_mod_cast hh.ne') this
  rw [← hJI, hJB, FractionalIdeal.coe_spanSingleton]

end GlobalTheory
end

