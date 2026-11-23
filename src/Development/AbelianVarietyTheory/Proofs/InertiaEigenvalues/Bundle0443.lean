module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0005
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDegree
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Topology

namespace GlobalTheory.UnramifiedDegree

theorem exists_degree : ∀ (l : ℕ) [Fact l.Prime],
    (∀ n : ℕ, 0 < n → ∀ σ : GQ l, ∃ a : ℕ, ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a) →
    (∀ n a b : ℕ, 0 < n → (∀ x : Om l, x ^ l ^ n = x → x ^ l ^ a = x ^ l ^ b) → a ≡ b [MOD n]) →
    ∃ z : GQ l → ℤ_[l], Continuous z ∧ (∀ σ τ, z (σ * τ) = z σ + z τ) ∧
      ∀ (σ : GQ l) (a : ℕ), (∀ n : ℕ, 0 < n → ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a) →
        z σ = (a : ℤ_[l]) := by
  intro l hl h1 h2
  have hpos : ∀ k : ℕ, 0 < l ^ k := fun k => pow_pos hl.out.pos k
  choose a ha using fun (σ : GQ l) (k : ℕ) => h1 (l ^ k) (hpos k) σ
  have hdv : ∀ (σ : GQ l) (k : ℕ), (l : ℤ) ^ k ∣ (a σ (k + 1) : ℤ) - (a σ k : ℤ) := by
    intro σ k
    have h := h2 (l ^ k) (a σ k) (a σ (k + 1)) (hpos k) fun x hx => by
      rw [← ha σ k x hx, ← ha σ (k + 1) x (by
        rw [pow_succ l k]; exact GlobalTheory.UnramifiedCrys.pow_pow_mul hx l)]
    exact_mod_cast h.dvd
  obtain ⟨z, hz⟩ : ∃ z : GQ l → ℤ_[l], ∀ σ k, PadicInt.toZModPow k (z σ) = (a σ k : ZMod (l ^ k)) := by
    refine ⟨fun σ => PadicInt.ofIntSeq _
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun k => (a σ k : ℤ)) l (hdv σ)), fun σ k => ?_⟩
    rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => (a σ k : ℤ)) l (hdv σ) k,
      Int.cast_natCast]
  have key : ∀ (σ : GQ l) (k b : ℕ), (∀ x : Om l, x ^ l ^ l ^ k = x → σ x = x ^ l ^ b) →
      PadicInt.toZModPow k (z σ) = (b : ZMod (l ^ k)) := by
    intro σ k b hb
    rw [hz, ZMod.natCast_eq_natCast_iff]
    exact h2 _ _ _ (hpos k) fun x hx => by rw [← ha σ k x hx, hb x hx]
  refine ⟨z, ?_, fun σ τ => ?_, fun σ b hb => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro σ₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
    have hev : ∀ᶠ σ in 𝓝 σ₀, ∀ x ∈ {y : Om l | y ^ l ^ l ^ k = y}, σ x = σ₀ x := by
      refine (GlobalTheory.UnramifiedCrys.finite_fixedPow (p := l) (R := Om l) (hpos k)).eventually_all.2
        fun x _ => ?_
      have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x).preimage
        (continuous_const_mul σ₀⁻¹)
      filter_upwards [ho.mem_nhds (show σ₀ ∈ _ by simp)] with σ hσ
      have h : σ₀⁻¹ (σ x) = x := hσ
      have h' := congrArg σ₀ h
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h'
    filter_upwards [hev] with σ hσ
    refine lt_of_le_of_lt ?_ hk
    rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, sub_eq_zero, hz σ₀]
    exact key σ k _ fun x hx => by rw [hσ x hx, ha σ₀ k x hx]
  · refine PadicInt.ext_of_toZModPow.mp fun k => ?_
    rw [map_add (f := _), hz σ, hz τ, ← Nat.cast_add]
    refine key _ k _ fun x hx => ?_
    rw [AlgEquiv.mul_apply, ha τ k x hx, map_pow, ha σ k x hx, ← pow_mul, ← pow_add]
  · refine PadicInt.ext_of_toZModPow.mp fun k => ?_
    rw [map_natCast]
    exact key σ k b (hb _ (hpos k))

end GlobalTheory.UnramifiedDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvrExtensionForMonicFamily
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

open Polynomial

theorem isLocalRing_of_domain_finite_padicInt (l : ℕ) [Fact l.Prime] (B : Type) [CommRing B]
    [IsDomain B] [Algebra ℤ_[l] B] [Module.Finite ℤ_[l] B] : IsLocalRing B := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun b => ?_
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, h1⟩ := hcon
  obtain ⟨E, hE, hM⟩ := GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem l b
  have e0 : E - 0 ∈ (Ideal.span {b}).restrictScalars ℤ_[l] := hM _ 0 fun n => by
    simp only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    exact dvd_pow_self b (Nat.succ_ne_zero n)
  have e1 : E - 1 ∈ (Ideal.span {1 - b}).restrictScalars ℤ_[l] := hM _ 1 fun n => by
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    have := one_sub_dvd_one_sub_pow b (n + 1)
    rw [← neg_sub 1 (b ^ (n + 1))]
    exact this.neg_right
  simp only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at e0 e1
  rcases (IsIdempotentElem.iff_eq_zero_or_one (p := E)).1 hE with h | h
  · rw [h, zero_sub] at e1
    exact h1 (isUnit_of_dvd_one (dvd_neg.1 e1))
  · rw [h] at e0
    exact h0 (isUnit_of_dvd_one e0)

theorem exists_fin_prod_of_splits {L : Type} [Field L] (t : ℕ) (f : L[X]) (hs : f.Splits)
    (hm : f.Monic) (ht : f.natDegree = t) : ∃ α : Fin t → L, f = ∏ c, (X - C (α c)) := by
  have hc : f.roots.toList.length = t := by
    rw [Multiset.length_toList, ← hs.natDegree_eq_card_roots, ht]
  subst hc
  refine ⟨f.roots.toList.get, ?_⟩
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm, ← Multiset.coe_toList f.roots]
  rw [Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
  congr 1
  conv_lhs => rw [← List.ofFn_get f.roots.toList]
  rw [List.map_ofFn]
  rfl

theorem exists_finite_dvr_splitting : ∀ (l : ℕ) [Fact l.Prime] {A ι : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] [Finite ι] (t : ℕ) (P : ι → Polynomial A), (∀ i, ((P i).map (toFr A)).Monic ∧ ((P i).map (toFr A)).natDegree = t) → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B), Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧ ∀ i, ∃ α : Fin t → FractionRing B, (P i).map ((toFr B).comp (algebraMap A B)) = ∏ c, (Polynomial.X - Polynomial.C (α c)) := by
  intro l _ A ι _ _ _ _ _ _ _ t P hP
  classical
  haveI := Fintype.ofFinite ι
  let K := FractionRing A
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing A
  let F : K[X] := ∏ i, (P i).map (toFr A)
  have hF : F.Monic := monic_prod_of_monic _ _ fun i _ => (hP i).1
  let L := F.SplittingField
  haveI : IsScalarTower A K L := inferInstance
  let S := integralClosure A L
  haveI : Module.Finite A S := IsIntegralClosure.finite A K L S
  haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain A K L S
  haveI : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension A K L S
  haveI : IsLocalRing S := by
    letI : Algebra ℤ_[l] S := ((algebraMap A S).comp (algebraMap ℤ_[l] A)).toAlgebra
    haveI : IsScalarTower ℤ_[l] A S := .of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℤ_[l] S := Module.Finite.trans A S
    exact isLocalRing_of_domain_finite_padicInt l S
  have hinj : Function.Injective (algebraMap A S) :=
    algebraMap_injective_of_field_isFractionRing A S K L
  have hnf : ¬ IsField S := fun h =>
    IsDiscreteValuationRing.not_isField A (isField_of_isIntegral_of_isField hinj h)
  haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 3 1).1
    (inferInstance : IsDedekindDomain S)
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hinj,
    fun i => ?_⟩
  let e : L ≃ₐ[S] FractionRing S := (FractionRing.algEquiv S L).symm
  have hsF : (F.map (algebraMap K L)).Splits := SplittingField.splits F
  have hsi : (((P i).map (toFr A)).map (algebraMap K L)).Splits :=
    hsF.of_dvd (hF.map _).ne_zero
      (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
  have hcomp : (toFr S).comp (algebraMap A S) =
      ((e : L →+* FractionRing S).comp (algebraMap K L)).comp (toFr A) := by
    ext a
    have : algebraMap K L (toFr A a) = algebraMap S L (algebraMap A S a) := by
      rw [← IsScalarTower.algebraMap_apply A S L]
      exact (IsScalarTower.algebraMap_apply A K L a).symm
    simp only [RingHom.comp_apply, this]
    exact (e.commutes _).symm
  rw [hcomp, ← Polynomial.map_map, ← Polynomial.map_map]
  refine exists_fin_prod_of_splits t _ (hsi.map _) (((hP i).1.map _).map _) ?_
  rw [natDegree_map, natDegree_map, (hP i).2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobInvMulMemIner
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

noncomputable section

namespace GlobalTheory.FrobLiftUnr

variable {l : ℕ} [Fact l.Prime]

theorem qK_bot : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (⊥ : IntermediateField ℚ_[l] (Om l)) = l := by
  have hK : FiniteDimensional ℚ_[l] (⊥ : IntermediateField ℚ_[l] (Om l)) := inferInstance
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.eK_mul_fK l ⊥ hK
  rw [IntermediateField.finrank_bot] at h
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.qK_eq_pow_fK l ⊥ hK, Nat.eq_one_of_mul_eq_one_left h, pow_one]

theorem exists_frob : ∃ Φ : GQ l, ∀ x : Om l, ‖x‖ ≤ 1 → ‖Φ x - x ^ l‖ < 1 := by
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrob (p := l) (K := (⊥ : IntermediateField ℚ_[l] (Om l)))
    inferInstance
  refine ⟨σ.restrictScalars ℚ_[l], fun x hx => ?_⟩
  have h := hσ x hx
  rw [qK_bot] at h
  exact h

theorem mem_GK_qlExt (Φ : GQ l) : Φ ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  unfold GK
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact Φ.commutes r

theorem max_unramified_le_unramified_ext (K' : FinExt l) :
    K0 K' ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l ((⊥ : IntermediateField ℚ_[l] (Om l))) := by
  refine (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l).trans ?_
  unfold MaximalUnramifiedExtension
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨m, -, hm, hx⟩
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_of_pow inferInstance hm hx

theorem max_unramified_eq_adjoin_roots (K' : FinExt l) : ∃ d : ℕ, 0 < d ∧
    K0 K' = IntermediateField.adjoin ℚ_[l] {ζ : Om l | ζ ^ (l ^ d - 1) = 1} := by
  have hQ : FiniteDimensional ℚ_[l] ((⊥ : IntermediateField ℚ_[l] (Om l))) := inferInstance
  have hK' : FiniteDimensional ℚ_[l] K'.1 := K'.2
  have hM : FiniteDimensional ℚ_[l] (K0 K') :=
    ReciprocityTheory.DiscreteGroups.LocalClassField.finDim_of_le l hK' (inf_le_left : K0 K' ≤ K'.1)
  obtain ⟨N, hN, hMN⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_le_Kn_of_le_Kur hQ hM (max_unramified_le_unramified_ext K')
  have hbot : (⊥ : IntermediateField ℚ_[l] (Om l)) ≤ K0 K' := bot_le
  have hd := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_pos (p := l) (K := (⊥ : IntermediateField ℚ_[l] (Om l))) hM
  have heq := ReciprocityTheory.DiscreteGroups.LocalClassField.eq_Kn_of_norm l ((⊥ : IntermediateField ℚ_[l] (Om l))) hQ hbot hd
    (ReciprocityTheory.DiscreteGroups.LocalClassField.finrank_eq_degLK_mul hbot hM)
    (fun x hx => ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn l ((⊥ : IntermediateField ℚ_[l] (Om l))) hQ hN (hMN hx))
  refine ⟨_, hd, heq.trans ?_⟩
  unfold ReciprocityTheory.DiscreteGroups.LocalClassField.Kn
  rw [qK_bot]
  exact bot_sup_eq _

theorem not_dvd_pow_sub_one {d : ℕ} (hd : 0 < d) : ¬ l ∣ l ^ d - 1 := by
  intro h
  have hp : l.Prime := Fact.out
  have h1 : l ∣ l ^ d := dvd_pow_self l hd.ne'
  have h2 : 1 ≤ l ^ d := Nat.one_le_pow _ _ hp.pos
  have h3 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem frobenius_lift_eq_on_maxUnramifiedSubfield (K' : FinExt l) (Φ : GQ l) (hΦ : ∀ x : Om l, ‖x‖ ≤ 1 → ‖Φ x - x ^ l‖ < 1)
    (σ : ↥(K0 K') →ₐ[ℚ_[l]] ↥(K0 K'))
    (hσ : ∀ x : ↥(K0 K'), ‖((x : ↥(K0 K')) : Om l)‖ ≤ 1 →
      ‖((σ x : ↥(K0 K')) : Om l) - ((x : ↥(K0 K')) : Om l) ^ l‖ < 1)
    (c : ↥(K0 K')) : Φ (c : Om l) = ((σ c : ↥(K0 K')) : Om l) := by
  obtain ⟨d, hd, hM⟩ := max_unramified_eq_adjoin_roots K'
  have hm := not_dvd_pow_sub_one (l := l) hd
  have hm0 : l ^ d - 1 ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero l)
  have key : ((Φ.toAlgHom.restrictScalars ℚ_[l]).comp (K0 K').val : ↥(K0 K') →ₐ[ℚ_[l]] Om l) =
      (K0 K').val.comp σ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[l] hM fun ζ hζ => ?_
    set z : ↥(K0 K') := ⟨ζ, hM ▸ IntermediateField.subset_adjoin ℚ_[l] _ hζ⟩ with hz
    change Φ ζ = ((σ z : ↥(K0 K')) : Om l)
    have hζ' : ζ ^ (l ^ d - 1) = 1 := hζ
    have hn : ‖ζ‖ = 1 := ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ'
    have h1 : (Φ ζ) ^ (l ^ d - 1) = 1 := by rw [← map_pow, hζ', map_one]
    have hz1 : z ^ (l ^ d - 1) = 1 := Subtype.ext hζ'
    have h2 : ((σ z : ↥(K0 K')) : Om l) ^ (l ^ d - 1) = 1 := by
      rw [← IntermediateField.coe_pow, ← map_pow, hz1, map_one]; rfl
    by_contra hne
    have e := ReciprocityTheory.DiscreteGroups.LocalClassField.norm_sub_eq_one_of_pow_eq_one l hm h1 h2 hne
    have a1 := hΦ ζ hn.le
    have a2 := hσ z hn.le
    have : ‖Φ ζ - ((σ z : ↥(K0 K')) : Om l)‖ < 1 := by
      have eq : Φ ζ - ((σ z : ↥(K0 K')) : Om l) =
          (Φ ζ - ζ ^ l) + (ζ ^ l - ((σ z : ↥(K0 K')) : Om l)) := by ring
      rw [eq]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt a1 ?_)
      rw [norm_sub_rev]; exact a2
    exact absurd e this.ne
  exact congrArg (fun f : ↥(K0 K') →ₐ[ℚ_[l]] Om l => f c) key

end GlobalTheory.FrobLiftUnr

namespace GlobalTheory.FrobLiftUnr

theorem exists_frob_inv_mul_mem_iner : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (Fr : Gl l), (pc Pl h hN hF hS).IsFrob Fr → ∃ Φ : Gl l, (∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Φ : GQ l) x - x ^ l‖ < 1) ∧ Φ⁻¹ * Fr ∈ (pc Pl h hN hF hS).Iner := by
  intro l _ Pl AI _ K' h hN hF hS Fr hFr
  obtain ⟨Φ, hΦ⟩ := exists_frob (l := l)
  refine ⟨⟨Φ, mem_GK_qlExt Φ⟩, fun x _ hx => hΦ x hx, ?_⟩
  intro c
  have hc := hFr c
  have key := frobenius_lift_eq_on_maxUnramifiedSubfield K' Φ hΦ (Pl.PD K').σ (Pl.PD_σ K') c
  have hc' : Pl.actQ Φ (algebraMap ↥(K0 K') Pl.R.B c) =
      algebraMap ↥(K0 K') Pl.R.B ((Pl.PD K').σ c) :=
    Pl.actQ_Kur Φ ⟨(c : Om l), (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l) c.2⟩
      ⟨(((Pl.PD K').σ c : ↥(K0 K')) : Om l), (inf_le_right : K0 K' ≤ MaximalUnramifiedExtension l) ((Pl.PD K').σ c).2⟩ key
  change (Pl.PD _).actB Fr _ = algebraMap ↥(K0 K') Pl.R.B ((Pl.PD K').σ c) at hc
  change (Pl.PD _).actB _ _ = _
  rw [Pl.PD_actB] at hc ⊢
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, AlgEquiv.mul_apply]
  change Pl.actQ Φ⁻¹ (Pl.actQ (Fr : GQ l) _) = _
  rw [hc, ← hc', ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]

end GlobalTheory.FrobLiftUnr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElemCyclotomicPeriodNotRootOfUnity
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BKLim.ZNotRoot

theorem pow_sub_one_sub {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    ∃ t : R, q ^ n - 1 - (n : R) * (q - 1) = (q - 1) ^ 2 * t := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨q * t + n, ?_⟩
    push_cast
    linear_combination q * ht

theorem eval_mul_sub {R : Type*} [CommRing R] (P : Polynomial R) (x q : R) :
    ∃ r : R, P.eval (q * x) - P.eval x = (q - 1) * x * (Polynomial.derivative P).eval x + (q - 1) ^ 2 * r := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨r, hr⟩ := hP
    obtain ⟨r', hr'⟩ := hQ
    refine ⟨r + r', ?_⟩
    simp only [Polynomial.eval_add, Polynomial.derivative_add]
    linear_combination hr + hr'
  | monomial n c =>
    obtain ⟨t, ht⟩ := pow_sub_one_sub q n
    refine ⟨c * x ^ n * t, ?_⟩
    have hd : x * (Polynomial.derivative (Polynomial.monomial n c)).eval x = c * n * x ^ n := by
      rw [Polynomial.derivative_monomial, Polynomial.eval_monomial]
      rcases n with _ | n
      · simp
      · simp only [Nat.add_sub_cancel]; push_cast; ring
    simp only [Polynomial.eval_monomial]
    linear_combination c * x ^ n * ht - (q - 1) * hd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem ev_coe (bk : BK K) (Q : Polynomial (Wq l bk.a)) :
    bk.ev (Q : bk.S) = (Q.map (wA l bk.a : Wq l bk.a →+* Ainf l)).eval (WittVector.teichmuller l bk.flat) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [Polynomial.coe_add, map_add (f := _), hP, hQ, Polynomial.map_add (f := _), Polynomial.eval_add]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X,
      map_mul, map_pow, bk.ev_C, bk.ev_X]
    simp

end GlobalTheory.BKLim.ZNotRoot

namespace GlobalTheory.BKLim.ZNotRoot
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem theta_deriv_ne (bk : BK K) : Per.θ l (bk.ev (Polynomial.derivative bk.Ep : bk.S)) ≠ 0 := by
  obtain ⟨c, A, B, h⟩ := GlobalTheory.BSP.bezout_Ep_derivative l K bk
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have h2 := congrArg (fun P : Polynomial (Wq l bk.a) => Per.θ l (bk.ev (P : bk.S))) h
  simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, map_add (f := _), map_mul, bk.ev_C] at h2
  intro h0
  change Per.θ l (bk.ev (A : bk.S)) * Per.θ l (bk.ev bk.E) + Per.θ l (bk.ev (B : bk.S)) * Per.θ l (bk.ev _) = _ at h2
  rw [hE, h0, mul_zero, mul_zero, add_zero, map_pow, map_natCast, map_pow, map_natCast] at h2
  have h3 := congrArg (fun x : OC l => (x : ℂ_[l])) h2
  simp only [ZeroMemClass.coe_zero] at h3
  push_cast at h3
  exact pow_ne_zero c (GlobalTheory.RingBasics.p_ne_zero (p := l)) h3.symm

end GlobalTheory.BKLim.ZNotRoot

namespace GlobalTheory.BKLim.ZNotRoot
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

abbrev Θ (l : ℕ) [Fact l.Prime] : Ainf l →+* ℂ_[l] := (Per.θD l).comp (aDp l)

theorem Θ_apply (x : Ainf l) : Θ l x = ((Per.θ l x : OC l) : ℂ_[l]) := (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1 x

theorem Θ_E (bk : BK K) : Θ l (bk.ev bk.E) = 0 := by
  rw [Θ_apply]
  have : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  rw [this]; rfl

theorem Θ_flat (bk : BK K) : Θ l (WittVector.teichmuller l bk.flat) ≠ 0 := by
  rw [Θ_apply, WittVector.fontaineTheta_teichmuller, ← (GlobalTheory.BSP.BK.prime_unif l K bk).2, coe_intToOC]
  intro h
  have h1 := congrArg norm h
  rw [PadicComplex.norm_extends, norm_zero, norm_eq_zero] at h1
  apply (GlobalTheory.BSP.BK.prime_unif l K bk).1.ne_zero
  exact Subtype.ext (Subtype.ext h1)

end GlobalTheory.BKLim.ZNotRoot

open GlobalTheory.BKLim.ZNotRoot in
theorem GlobalTheory.BKLim.exists_isZ_not_root : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (g : ↥(GK K)) (z : ℂ_[l]), IsZ bk g z ∧ ∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1 := by
  intro l _ K bk
  obtain ⟨τ, hτ⟩ := GlobalTheory.BSP.exists_isPer l K bk
  obtain ⟨hφ, ε, η, hε, hη⟩ := id hτ
  set u : Ainf l := WittVector.teichmuller l bk.flat with hu_def
  set D : Ainf l := bk.ev (Polynomial.derivative bk.Ep : bk.S) with hD_def
  set a : ℂ_[l] := Θ l ((↑η⁻¹ : Ainf l) * τ * u * D) with ha_def
  have ha : a ≠ 0 := by
    rw [ha_def, map_mul, map_mul, map_mul]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) (Θ_flat bk)) ?_
    · exact ((Units.isUnit η⁻¹).map (Θ l)).ne_zero
    · simpa using _root_.GlobalTheory.ThetaPer.thetaD_aDp_pow_ne_zero l K bk τ hτ 1
    · rw [Θ_apply]; intro h
      apply theta_deriv_ne bk
      exact Subtype.ext h
  obtain ⟨k, hk0, hk⟩ := _root_.GlobalTheory.SmallRootCl.exists_one_add_pow_mul_not_root l a ha
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.BSP.galois_moves_flat_by_unit_root l (_root_.GlobalTheory.rootOfUnity_mem_range_Om l) K bk (ε ^ (l ^ k)) (by rw [map_pow, hε.1, one_pow])
  set μ : Ainf l := WittVector.teichmuller l ε - 1 with hμ_def
  set E : Ainf l := bk.ev bk.E with hE_def
  set P : Polynomial (Ainf l) := bk.Ep.map (wA l bk.a : Wq l bk.a →+* Ainf l) with hP_def
  have hEP : E = P.eval u := ev_coe bk bk.Ep
  have hDP : D = (Polynomial.derivative P).eval u := by
    rw [hD_def, ev_coe, hP_def, Polynomial.derivative_map]
  have hσu : Per.σA (g : GQ l) u = WittVector.teichmuller l ε ^ (l ^ k) * u := by
    rw [hu_def, GlobalTheory.RingIface.sigA_teich, hg, map_mul, map_pow]
  have hσE : Per.σA (g : GQ l) E = P.eval (WittVector.teichmuller l ε ^ (l ^ k) * u) := by
    rw [hEP, hP_def, Polynomial.eval_map, Polynomial.hom_eval₂, hσu, ← Polynomial.eval_map]
    congr 2
    exact RingHom.ext fun w => bk.gal_w g w
  obtain ⟨r, hr⟩ := eval_mul_sub P u (WittVector.teichmuller l ε ^ (l ^ k))
  obtain ⟨s, hs⟩ := pow_sub_one_sub (WittVector.teichmuller l ε) (l ^ k)
  have hμE : μ = (↑η⁻¹ : Ainf l) * E * τ := by
    have h1 : (η : Ainf l) * μ = E * τ := by rw [hμ_def, ← hη, hφ]
    calc μ = (↑η⁻¹ : Ainf l) * ((η : Ainf l) * μ) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [h1]; ring
  set L : Ainf l := ((l ^ k : ℕ) : Ainf l) with hL_def
  have hq : WittVector.teichmuller l ε ^ (l ^ k) - 1 = (↑η⁻¹ : Ainf l) * E * τ * (L + μ * s) := by
    rw [← hμE, hμ_def]; linear_combination hs
  set w : Ainf l := 1 + (↑η⁻¹ : Ainf l) * τ * (L + μ * s) * u * D +
    E * ((↑η⁻¹ : Ainf l) * τ) ^ 2 * (L + μ * s) ^ 2 * r with hw_def
  have hw : Per.σA (g : GQ l) E = E * w := by
    rw [hσE, hw_def, hDP]
    rw [hq] at hr
    linear_combination hr - hEP
  have hΘw : Θ l w = 1 + (l : ℂ_[l]) ^ k * a := by
    have hΘE : Θ l E = 0 := Θ_E bk
    rw [hw_def, ha_def, hL_def, hμE]
    simp only [map_add (f := _), map_mul, map_pow, map_one, hΘE, map_natCast]
    push_cast
    ring
  refine ⟨g, (Θ l w)⁻¹, ⟨w, hw, ?_⟩, fun i hi => ?_⟩
  · change (Θ l w)⁻¹ * Θ l w = 1
    rw [hΘw]; exact inv_mul_cancel₀ hk0
  · rw [inv_pow, Ne, inv_eq_one, hΘw]
    exact hk i hi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerCocycleTiltUniformizerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummer_cocycle_tilt_uniformizer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), ∃ c : ↥(GK K) → ℤ_[l],
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) ∧ ∀ g, bk.FixFlat g → c g = 0 := by
  first | (exact @GlobalTheory.FlatKummer.exists_kummer_flat) | (exact GlobalTheory.FlatKummer.exists_kummer_flat) | (intros; apply GlobalTheory.FlatKummer.exists_kummer_flat  <;> assumption)
end

