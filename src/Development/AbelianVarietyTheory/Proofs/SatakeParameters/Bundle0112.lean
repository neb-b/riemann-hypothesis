module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsPowValEqZpow
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

namespace GlobalTheory.TotDisjUnlinked

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_val_eq_zpow (s : ℂ) (x : kˣ) :
    (absPow k s x : ℂ) = ((resCard k : ℂ) ^ (-s)) ^ (SmGL.ord k x : ℤ) := by
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
  have hq' : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [val_absPow, LGrp.nabs_eq_zpow, Complex.cpow_def_of_ne_zero (by exact_mod_cast (zpow_pos hq _).ne'),
    Complex.cpow_def_of_ne_zero hq', ← Complex.ofReal_log (zpow_pos hq _).le, Real.log_zpow,
    ← Complex.exp_int_mul, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem absPow_eq_unrChar (s : ℂ) :
    absPow k s = unrChar k (Units.mk0 ((resCard k : ℂ) ^ (-s))
      (by
        have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
        exact Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hq.ne')))) := by
  ext x
  rw [absPow_val_eq_zpow, unrChar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

end GlobalTheory.TotDisjUnlinked

theorem GlobalTheory.TotDisjUnlinked.main :
    GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.UnlinkedProductIrreducible := by
  intro H k _ _ _ _ r t s s' π₁ π₂ d d' σ σ' h₁ h₂ hu
  refine H k r t s s' π₁ π₂ d d' σ σ' h₁ h₂ fun a b h j _ => ?_
  rw [GlobalTheory.TotDisjUnlinked.absPow_eq_unrChar]
  exact hu a b h _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig

theorem residue_map_equiv {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R ≃+* R') {a b : R} (h : IsLocalRing.residue R a = IsLocalRing.residue R b) :
    IsLocalRing.residue R' (φ a) = IsLocalRing.residue R' (φ b) := by
  have h' : IsLocalRing.residue R (a - b) = 0 := by rw [map_sub, h, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at h'
  rw [← sub_eq_zero, ← map_sub, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  refine (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => ?_)
  exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h') ((isUnit_map_iff φ _).1 hu)

theorem heckeD_add (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (Formalism.AUTREP.GAf L n)) (Dset : Set (Formalism.AUTREP.GAf L n))
    (hfin : ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Dset).Finite)
    (c : ℂ) (f f' : Formalism.AUTREP.GAf L n → W) :
    Formalism.L2.NG.heckeD J Dset (c • f + f') = c • Formalism.L2.NG.heckeD J Dset f + Formalism.L2.NG.heckeD J Dset f' := by
  classical
  funext g
  have hsub : ∀ F : Formalism.AUTREP.GAf L n → W,
      Function.support (fun cc : Formalism.AUTREP.GAf L n ⧸ J =>
        if hc : ∃ x ∈ Dset, (x : Formalism.AUTREP.GAf L n ⧸ J) = cc then F (g * hc.choose) else 0) ⊆
        (hfin.toFinset : Set (Formalism.AUTREP.GAf L n ⧸ J)) := by
    intro F cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dite_eq_right]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [Pi.add_apply, Pi.smul_apply]
  simp only [Formalism.L2.NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ (hsub _), finsum_eq_sum_of_support_subset _ (hsub _),
    finsum_eq_sum_of_support_subset _ (hsub _), Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun cc _ => ?_
  split_ifs <;> simp

theorem cls_eq_of_residue : ∀ {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O] (S : Set (Module.End K V)) (ψ ψ' : Algebra.adjoin O S →ₐ[O] O), (∀ a (h : a ∈ S), IsLocalRing.residue O (ψ ⟨a, Algebra.subset_adjoin h⟩) = IsLocalRing.residue O (ψ' ⟨a, Algebra.subset_adjoin h⟩)) → Formalism.L2.NCov.cls ψ = Formalism.L2.NCov.cls ψ' := by
  first
  | exact @_root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators
  | exact _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators
  | (apply _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators ..)

theorem pt_of_eigvec : ∀ {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (S : Set (Module.End K V)) (e : V), e ≠ 0 → Function.Injective (algebraMap O K) → (∀ a ∈ S, ∃ c : O, a e = algebraMap O K c • e) → ∃ ψ : Algebra.adjoin O S →ₐ[O] O, (∀ t : Algebra.adjoin O S, (t : Module.End K V) e = algebraMap O K (ψ t) • e) ∧ e ∈ Formalism.L2.NCov.W (Algebra.adjoin O S) (Formalism.L2.NCov.pt ψ) := by
  intro O K V _ _ _ _ _ _ _ S e he hinj hS
  have key : ∀ t ∈ Algebra.adjoin O S, ∃ c : O, t e = algebraMap O K c • e := by
    intro t ht
    induction ht using Algebra.adjoin_induction with
    | mem a ha => exact hS a ha
    | algebraMap r => exact ⟨r, by rw [Formalism.L2.NCov.algebraMap_end_eq]; simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨c1, h1⟩ := iha
      obtain ⟨c2, h2⟩ := ihb
      exact ⟨c1 + c2, by rw [LinearMap.add_apply, h1, h2, map_add (f := _), add_smul]⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨c1, h1⟩ := iha
      obtain ⟨c2, h2⟩ := ihb
      exact ⟨c1 * c2, by rw [Module.End.mul_apply, h2, map_smul, h1, smul_smul, map_mul, mul_comm]⟩
  choose f hf using fun t : Algebra.adjoin O S => key t t.2
  have uniq : ∀ c c' : O, algebraMap O K c • e = algebraMap O K c' • e → c = c' :=
    fun c c' hcc => hinj (smul_left_injective K he hcc)
  have f1 : f 1 = 1 := uniq _ _ (by rw [← hf 1, map_one, one_smul]; rfl)
  have fm : ∀ s t, f (s * t) = f s * f t := fun s t => uniq _ _ (by
    rw [← hf (s * t), map_mul, mul_comm, mul_smul, ← hf s, ← map_smul, ← hf t]; rfl)
  have f0 : f 0 = 0 := uniq _ _ (by rw [← hf 0, map_zero, zero_smul]; rfl)
  have fa : ∀ s t, f (s + t) = f s + f t := fun s t => uniq _ _ (by
    rw [← hf (s + t), map_add (f := _), add_smul, ← hf s, ← hf t]; rfl)
  have fc : ∀ r, f (algebraMap O (Algebra.adjoin O S) r) = r := fun r => uniq _ _ (by
    rw [← hf]
    show (algebraMap O (Module.End K V) r) e = _
    rw [Formalism.L2.NCov.algebraMap_end_eq]; simp)
  let ψ : Algebra.adjoin O S →ₐ[O] O :=
    { toFun := f, map_one' := f1, map_mul' := fm, map_zero' := f0, map_add' := fa, commutes' := fc }
  refine ⟨ψ, fun t => hf t, ?_⟩
  refine (Submodule.mem_iInf _).2 fun t => ?_
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨1, ?_⟩
  simp only [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Formalism.L2.NCov.pt]
  rw [hf t]
  exact sub_self _

theorem descent : ∀ {K C : Type} [Field K] [Field C] (φ : K →+* C) {ι : Type} [Fintype ι] {G : Type} (Mg : G → Matrix ι ι K) (d : ι → C), d ≠ 0 → (∀ g, Matrix.mulVec ((Mg g).map φ) d = 0) → ∃ c : ι → K, c ≠ 0 ∧ ∀ g, Matrix.mulVec (Mg g) c = 0 := by
  intro K C _ _ φ ι _ G Mg d hd hdg
  classical
  by_contra hne
  push_neg at hne
  let kerS : Finset G → Submodule K (ι → K) := fun s => ⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (Mg g))
  have hex : ∃ m, ∃ s : Finset G, Module.finrank K (kerS s) = m := ⟨_, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hmin : ∀ s' : Finset G, Module.finrank K (kerS s) ≤ Module.finrank K (kerS s') := fun s' =>
    hs ▸ Nat.find_min' hex ⟨s', rfl⟩
  have hbot : kerS s = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Submodule.mem_bot]
    by_contra hc0
    obtain ⟨g, hg⟩ := hne c hc0
    have hins : kerS (insert g s) = LinearMap.ker (Matrix.mulVecLin (Mg g)) ⊓ kerS s := by
      simp only [kerS, Finset.iInf_insert]
    have hle : kerS (insert g s) ≤ kerS s := by rw [hins]; exact inf_le_right
    have heq := Submodule.eq_of_le_of_finrank_le hle (hmin _)
    have hc' : c ∈ kerS (insert g s) := heq ▸ hc
    rw [hins] at hc'
    exact hg (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hc').1)
  let R : Matrix (↥s × ι) ι K := fun p b => Mg p.1.1 p.2 b
  have hinjR : Function.Injective (Matrix.toLin' R) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [← hbot]
    simp only [kerS, Submodule.mem_iInf, LinearMap.mem_ker]
    intro g hg
    funext a
    have hc' : Matrix.mulVec R c = 0 := by rw [← Matrix.toLin'_apply]; exact LinearMap.mem_ker.1 hc
    have := congrFun hc' (⟨g, hg⟩, a)
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, R] using this
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' R) (LinearMap.ker_eq_bot.2 hinjR)
  have hLR : LinearMap.toMatrix' Ψ * R = 1 := by
    have := congrArg LinearMap.toMatrix' hΨ
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at this
  have hLRC : (LinearMap.toMatrix' Ψ).map φ * R.map φ = 1 := by
    rw [← Matrix.map_mul, hLR, Matrix.map_one φ φ.map_zero φ.map_one]
  have hRd : Matrix.mulVec (R.map φ) d = 0 := by
    funext p
    have := congrFun (hdg p.1.1) p.2
    simp only [Matrix.mulVec, dotProduct] at this
    exact this
  apply hd
  calc d = Matrix.mulVec ((LinearMap.toMatrix' Ψ).map φ * R.map φ) d := by rw [hLRC, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hRd, Matrix.mulVec_zero]

theorem coeff_monic_poly_sum {R : Type} [Semiring R] (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n) (c : ℕ → R) :
    (X ^ n + ∑ k' ∈ Finset.Icc 1 n, C (c k') * X ^ (n - k')).coeff (n - k) = c k := by
  rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b hb hbk
    rw [coeff_C_mul_X_pow, if_neg]
    rw [Finset.mem_Icc] at hb
    omega
  · intro hk
    exact absurd (Finset.mem_Icc.2 ⟨hk1, hk2⟩) hk

theorem coeff_extract : ∀ {O : Type} [CommRing O] [IsLocalRing O] (ι : O →+* ℂ), Function.Injective ι → ∀ (n q : ℕ), IsUnit (q : O) → ∀ (p : O[X]) (lam : ℕ → ℂ) (t : ℕ → O), p.map ι = X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (n - k) → p.map (IsLocalRing.residue O) = (X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : O) ^ k * (q : O) ^ (k * (k - 1) / 2) * t k) * X ^ (n - k)).map (IsLocalRing.residue O) → ∀ k, 1 ≤ k → k ≤ n → ∃ a : O, ι a = lam k ∧ IsLocalRing.residue O a = IsLocalRing.residue O (t k) := by
  intro O _ _ ι hι n q hq p lam t h1 h2 k hk1 hk2
  set u : O := (-1 : O) ^ k * (q : O) ^ (k * (k - 1) / 2) with hu_def
  have hu : IsUnit u := ((isUnit_one.neg).pow k).mul (hq.pow _)
  have e1 : ι (p.coeff (n - k)) = ι u * lam k := by
    have := congrArg (fun P : ℂ[X] => P.coeff (n - k)) h1
    simp only [coeff_map] at this
    rw [this, coeff_monic_poly_sum n k hk1 hk2 (fun k' => (-1) ^ k' * (q : ℂ) ^ (k' * (k' - 1) / 2) * lam k')]
    simp [u]
  have e2 : IsLocalRing.residue O (p.coeff (n - k)) = IsLocalRing.residue O (u * t k) := by
    have := congrArg (fun P : (IsLocalRing.ResidueField O)[X] => P.coeff (n - k)) h2
    simp only [coeff_map] at this
    rw [this, coeff_monic_poly_sum n k hk1 hk2 (fun k' => (-1 : O) ^ k' * (q : O) ^ (k' * (k' - 1) / 2) * t k')]
  refine ⟨↑hu.unit⁻¹ * p.coeff (n - k), ?_, ?_⟩
  · rw [map_mul, e1, ← mul_assoc, ← map_mul, hu.val_inv_mul, map_one, one_mul]
  · rw [map_mul, e2, ← map_mul, ← mul_assoc, hu.val_inv_mul, one_mul]

theorem normV_unit : ∀ (D : D7) (i : D.nd.Loc) (w : PlE D.host), w ∉ placesOver D.host.E (D.nd.l i) → IsUnit (((normV w : ℕ) : D.nd.O i)) := by
  intro D i w hw
  classical
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hN : ¬ (D.nd.l i) ∣ normV w := by
    intro hdvd
    letI := Ideal.Quotient.field w.asIdeal
    haveI : Finite (𝓞 D.host.E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    letI := Fintype.ofFinite (𝓞 D.host.E ⧸ w.asIdeal)
    obtain ⟨p, hchar⟩ := CharP.exists (𝓞 D.host.E ⧸ w.asIdeal)
    have hp : p.Prime := CharP.char_is_prime (𝓞 D.host.E ⧸ w.asIdeal) p
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 D.host.E ⧸ w.asIdeal) p
    have hcard : normV w = p ^ (n : ℕ) := by rw [normV, Nat.card_eq_fintype_card, hn]
    rw [hcard] at hdvd
    have hlp : D.nd.l i = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow hdvd)
    apply hw
    show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hlp]
    exact CharP.cast_eq_zero _ p
  have hu : IsUnit ((normV w : ℕ) : ℤ_[D.nd.l i]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hN
  have := hu.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))
  rwa [map_natCast] at this

end GlobalTheory.PtLocalEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorLowerBoundOfPlaceBoundWitt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU.LowGen

theorem le_order_subst' {σ τ K : Type} [Finite σ] [Field K] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ K) :
    f.order ≤ (MvPowerSeries.subst a f).order := by
  refine le_trans ?_ (MvPowerSeries.le_order_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) f)
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
    le_iInf fun i => MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (ha i)
  calc f.order = 1 * f.order := (one_mul _).symm
    _ ≤ _ := by gcongr

theorem applyD_eq_zero {σ τ K : Type} [Field K] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ K)
    (h : ((P.totalDegree + 1 : ℕ) : ℕ∞) ≤ f.order) : applyD P f = 0 := by
  unfold applyD
  refine Finset.sum_eq_zero fun n hn => ?_
  have h1 : n.degree ≤ P.totalDegree := MvPolynomial.le_totalDegree hn
  have h2 : MvPowerSeries.coeff n f = 0 := by
    apply MvPowerSeries.coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h
    exact_mod_cast Nat.lt_succ_of_le h1
  rw [h2, mul_zero, zero_smul]

noncomputable def applyDL {σ τ : Type} (K : Type) [Field K] (P : MvPolynomial σ (MvPolynomial τ ℤ)) :
    MvPowerSeries σ K →ₗ[K] MvPolynomial τ K where
  toFun := applyD P
  map_add' f g := by
    simp only [applyD, map_add (f := _), mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [applyD, RingHom.id_apply, Finset.smul_sum, smul_smul, MvPowerSeries.coeff_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    ring

theorem applyD_map {σ τ K L : Type} [Field K] [Field L] (φ : K →+* L) (P : MvPolynomial σ (MvPolynomial τ ℤ))
    (f : MvPowerSeries σ K) :
    applyD P (MvPowerSeries.map φ f) = MvPolynomial.map φ (applyD P f) := by
  unfold applyD
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map φ), MvPolynomial.map_C,
    MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom L)]
  simp

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_coordZA (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ) (s : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K j s) = 0 := by
  rcases s with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

theorem map_coordZA (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ) (s : X.EA j ⊕ X.EA j) :
    MvPowerSeries.map (algebraMap (K0 p) K) (X.coordZA (K0 p) j s) = X.coordZA K j s := by
  rcases s with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

theorem ThZA_map (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ)
    (f : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) :
    X.ThZA K j (MvPowerSeries.map (algebraMap (K0 p) K) f) =
      MvPowerSeries.map (algebraMap (K0 p) K) (X.ThZA (K0 p) j f) := by
  unfold Sys.ThZA
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_coordZA X _ j))]
  congr 1
  funext s
  exact (map_coordZA X K j s).symm

theorem p_ne_zero (K : Type) [Field K] [Algebra (K0 p) K] : (p : K) ≠ 0 := by
  have h : (p : WW p) ≠ 0 := WittVector.p_nonzero p (kb p)
  have h2 := (map_ne_zero_iff _ (IsFractionRing.injective (WW p) (K0 p))).mpr h
  have h3 := (map_ne_zero (algebraMap (K0 p) K)).mpr h2
  simpa using h3

theorem geC_of_mem {X : Sys p} (Y : Pend X) (g : ℝ) (y : Y.Kc) (hy : y ∈ Y.Oc) :
    Y.geC ((p : Y.Kc) ^ ⌈g⌉ * y) g := by
  intro a b hb hab
  have hp := p_ne_zero (p := p) Y.Kc
  have h1 : a ≤ ⌈g⌉ * b := by
    have : (a : ℝ) ≤ (⌈g⌉ : ℝ) * b := hab.trans (mul_le_mul_of_nonneg_right (Int.le_ceil g) (Nat.cast_nonneg b))
    exact_mod_cast this
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h1)
  have : ((p : Y.Kc) ^ ⌈g⌉ * y) ^ b * (p : Y.Kc) ^ (-a) = (p : Y.Kc) ^ k * y ^ b := by
    rw [mul_pow, ← zpow_natCast ((p : Y.Kc) ^ ⌈g⌉), ← zpow_mul, mul_right_comm, ← zpow_add₀ hp, ← sub_eq_add_neg, hk,
      zpow_natCast]
  rw [this]
  exact Y.Oc.mul_mem (Y.Oc.pow_mem (natCast_mem Y.Oc p) _) (Y.Oc.pow_mem hy _)

theorem cofactor_lower_bound_of_place_bound_witt : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ) (v : X.Pl) (g : ℝ),
    MvPowerSeries.constantCoeff Y.be = 0 → IsPlaceCofactorValuationLowerBound X Y.be j v g → Y.LowAt j v g := by
  intro p _ X Y j v g _ hL U hU I m
  choose Un hUn using _root_.GlobalTheory.TwU.monomial_param_as_log_series p (X.EA j ⊕ X.EA j)
  set P := X.PIv j I v with hP
  set d := P.totalDegree with hd
  have hfin : {n : (X.EA j ⊕ X.EA j) →₀ ℕ | n.degree ≤ d}.Finite := Finsupp.finite_of_degree_le d
  set S := hfin.toFinset with hS
  have hspan := GlobalTheory.T.lowCoefficients_of_parameterCoefficients p (X.EA j ⊕ X.EA j) Y.Kc Un hUn U d S (fun n hn => hfin.mem_toFinset.mpr hn)
  have hint : ∀ n, IntS p (inParam p (Un n)) := fun n =>
    ⟨MvPowerSeries.monomial n 1, by rw [(hUn n).1, MvPowerSeries.map_monomial, RingHom.map_one]⟩
  choose a ha using fun n => hL (Un n) (hint n) I m
  have hE : Y.PhAt j v = phAt X Y.be j v := rfl
  rw [hE]
  set E := expS p (-phAt X Y.be j v) with hEdef
  set φ := algebraMap (K0 p) Y.Kc with hφ
  set c : _ → Y.Kc := fun n => MvPowerSeries.coeff n (inParamK p Y.Kc U) with hc
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_coordZA X Y.Kc j)
  set A := U - ∑ n ∈ S, c n • MvPowerSeries.map φ (Un n) with hA
  have hAo : ((d + 1 : ℕ) : ℕ∞) ≤ A.order := by
    apply MvPowerSeries.nat_le_order
    intro k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hA, map_sub, hspan k (Nat.le_of_lt_succ hk), map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map]
  have hz : applyD P (X.ThZA Y.Kc j (MvPowerSeries.map φ E * A)) = 0 := by
    apply applyD_eq_zero
    refine le_trans ?_ (le_order_subst' (constantCoeff_coordZA X Y.Kc j) _)
    exact hAo.trans (le_trans le_add_self MvPowerSeries.le_order_mul)
  have hU' : MvPowerSeries.map φ E * U =
      MvPowerSeries.map φ E * A + ∑ n ∈ S, c n • MvPowerSeries.map φ (E * Un n) := by
    rw [hA, mul_sub, Finset.mul_sum]
    simp only [mul_smul_comm, map_mul, sub_add_cancel]
  have hTh : ∀ f, applyD P (X.ThZA Y.Kc j f) =
      ((applyDL Y.Kc P) ∘ₗ (MvPowerSeries.substAlgHom (R := Y.Kc) hsub).toLinearMap) f := by
    intro f
    rw [Sys.ThZA, ← MvPowerSeries.coe_substAlgHom hsub]
    rfl
  have hval : AddMonoidAlgebra.coeff (applyD P (X.ThZA Y.Kc j (MvPowerSeries.map φ E * U))) m =
      (p : Y.Kc) ^ ⌈g⌉ * ∑ n ∈ S, c n * φ (algebraMap (WW p) (K0 p) (a n)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hU', hTh, map_add (f := _), ← hTh, hz, zero_add, map_sum, MvPolynomial.coeff_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, ← hTh, hφ, ThZA_map, applyD_map, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, ha n, map_mul,
      map_zpow₀, map_natCast, smul_eq_mul]
    ring
  rw [hval]
  exact geC_of_mem Y g _ (Y.Oc.sum_mem fun n _ => Y.Oc.mul_mem (hU n) (Y.witt_mem_integers_Cp _))

end GlobalTheory.TwU.LowGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamPullbackAlongSecondMapSmulIotaMultiKaehler
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.WH GlobalTheory.PD GlobalTheory.W1 GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

namespace GlobalTheory.WH.PullCoc

section Gen

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E E' : Type} [AddCommGroup E] [Module k E]
  [AddCommGroup E'] [Module k E']

end Gen

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section J2

variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K']

theorem mapDR_smul_ιMulti {L : Type} [Field L] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] (b : K) (q : ℕ) (v : Fin q → K) :
    mapDR ℂ K L (b • ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      algebraMap K L b • ExteriorAlgebra.ιMulti L q fun j => D ℂ L (algebraMap K L (v j)) := by
  rw [map_smul, algebraMap_smul]
  congr 1
  simp [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, mapDR, map1, Function.comp_def,
    KaehlerDifferential.map_D]

theorem deRhamPullbackAlongSecondMap_smul_iotaMulti_kaehlerD (j2 : K →ₐ[ℂ] K') (b : K) (q : ℕ) (v : Fin q → K) :
    pr2L j2 (b • ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      j2 b • ExteriorAlgebra.ιMulti K' q fun j => D ℂ K' (j2 (v j)) := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_smul_ιMulti (L := K') b q v

end J2

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

end
end

