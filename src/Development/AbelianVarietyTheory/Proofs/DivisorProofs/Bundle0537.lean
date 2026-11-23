module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIndexValuationCompat
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CommonValuation

theorem exists_eq_pow {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    (P : HeightOneSpectrum R) (u : Valuation F (WithZero (Multiplicative ℤ)))
    (h1 : ∀ r : R, u (algebraMap R F r) ≤ 1) (h2 : ∀ r : R, u (algebraMap R F r) < 1 ↔ r ∈ P.asIdeal) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : F, u x = P.valuation F x ^ e := by
  have hu : ∀ r : R, r ∉ P.asIdeal → u (algebraMap R F r) = 1 := fun r hr =>
    le_antisymm (h1 r) (not_lt.1 fun h => hr ((h2 r).1 h))
  have hone : ∀ x : F, P.valuation F x = 1 → u x = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x hx.le
    have hn : n ∉ P.asIdeal := by
      rw [← P.valuation_eq_one_iff_notMem (K := F), ← h, map_mul, hx, one_mul]
      exact (P.valuation_eq_one_iff_notMem (K := F)).2 d.2
    have := congrArg u h
    rwa [map_mul, hu _ d.2, hu _ hn, mul_one] at this
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ' : P.valuation F (algebraMap R F π) = WithZero.exp (-1) := (P.valuation_of_algebraMap π).trans hπ
  have l1 : (WithZero.exp (-1) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπ0 : algebraMap R F π ≠ 0 := fun h => by
    rw [h, map_zero] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  have hlt : u (algebraMap R F π) < 1 := (h2 π).2 ((P.valuation_lt_one_iff_mem (K := F) π).1 (hπ' ▸ l1))
  have hu0 : u (algebraMap R F π) ≠ 0 := by simpa using hπ0
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (u (algebraMap R F π)) = -(e : ℤ) ∧ 0 < e := by
    rw [← WithZero.exp_log hu0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    exact ⟨(-WithZero.log (u (algebraMap R F π))).toNat, by omega, by omega⟩
  refine ⟨e, he.2, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he.2.ne']
  have h0 : P.valuation F x ≠ 0 := by simpa using hx
  have h3 := hone (x * algebraMap R F π ^ WithZero.log (P.valuation F x)) (by
    rw [map_mul, map_zpow₀, hπ', ← WithZero.exp_zsmul]
    nth_rewrite 1 [← WithZero.exp_log h0]
    rw [← WithZero.exp_add]; simp)
  rw [map_mul, map_zpow₀, ← WithZero.exp_log hu0, he.1, ← WithZero.exp_zsmul,
    mul_eq_one_iff_eq_inv₀ WithZero.exp_ne_zero, ← WithZero.exp_neg] at h3
  rw [h3]
  nth_rewrite 2 [← WithZero.exp_log h0]
  rw [← WithZero.exp_nsmul]
  congr 1
  simp [mul_comm]

theorem le_one_of_ringOfIntegers {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ)
    (r : 𝓞 F) : u (algebraMap (𝓞 F) F r) ≤ 1 :=
  (Valuation.integer.integers u).isIntegral_iff_v_le_one.1 r.isIntegral_coe.tower_top

theorem exists_centre {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ) :
    ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧ ∀ r, r ∈ Q ↔ u (algebraMap (𝓞 F) F r) < 1 := by
  refine ⟨{ carrier := {r | u (algebraMap (𝓞 F) F r) < 1}
            add_mem' := fun {a b} ha hb => ?_
            zero_mem' := by simp
            smul_mem' := fun c r hr => ?_ }, ⟨?_, fun {a b} h => ?_⟩, fun _ => Iff.rfl⟩
  · change u _ < 1
    rw [map_add (f := _)]
    exact u.map_add_lt ha hb
  · change u _ < 1
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (le_one_of_ringOfIntegers u c)).trans_lt hr
  · rw [Ideal.ne_top_iff_one]
    change ¬ u _ < 1
    simp
  · by_contra! hn
    have ha : u (algebraMap _ F a) = 1 := le_antisymm (le_one_of_ringOfIntegers u a) (not_lt.1 hn.1)
    have hb : u (algebraMap _ F b) = 1 := le_antisymm (le_one_of_ringOfIntegers u b) (not_lt.1 hn.2)
    change u _ < 1 at h
    rw [map_mul, map_mul, ha, hb, mul_one] at h
    exact lt_irrefl _ h

end GlobalTheory.CommonValuation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
section
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory

namespace GlobalTheory

namespace PDiv

variable {p : ℕ} [hp : Fact p.Prime] {R A : Type} [CommRing R] [CommRing A]

theorem exists_dualSystem (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ s : Finset (CartierDual R M × M), ∀ a, ∑ i ∈ s, i.1 a • i.2 = a := by
  obtain ⟨u, hu⟩ :=
    (dualTensorHom_bijective_of_finite_projective_right (R := R) (M := M) (N := M)).2 LinearMap.id
  obtain ⟨u, rfl⟩ := (LinearEquiv.rTensor M (CartierDual.toDual R M)).surjective u
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset u
  exact ⟨s, fun a => by simpa [CartierDual.toDual] using LinearMap.congr_fun hu a⟩

variable [Bialgebra R A]

theorem dUnit_pow_prime (h : (p : R) = 0) (a : A) : dUnit (R := R) (a ^ p) = 0 := by
  have key : ∀ k : ℕ, dUnit (R := R) (a ^ (k + 1)) =
      ((k + 1 : ℕ) * counitAlgHom R A a ^ k : R) • dUnit (R := R) a := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, dUnit, AugCot.d_mul, ← dUnit, ← dUnit, ih, smul_smul, ← add_smul, map_pow]
      congr 1
      push_cast
      ring
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
  have := key k
  rwa [← Nat.succ_eq_add_one, ← hk, h, zero_mul, zero_smul] at this

variable [IsCocomm R A]

theorem convPow_prime_apply (h : (p : R) = 0) {B ι : Type} [CommRing B] [Algebra R B] (s : Finset ι)
    (φ : ι → CartierDual R A) (b : ι → B) (f : A →ₗ[R] B) (hf : ∀ a, f a = ∑ i ∈ s, φ i a • b i)
    (a : A) : (toConv f ^ p) a = ∑ i ∈ s, (φ i ^ p) a • b i ^ p := by
  let j : CartierDual R A →* WithConv (A →ₗ[R] B) :=
    { toFun := fun χ => toConv ((Algebra.ofId R B).toLinearMap ∘ₗ χ.ofConv)
      map_one' := rfl
      map_mul' := fun χ ψ => congrArg toConv (LinearMap.algHom_comp_convMul_distrib _ χ ψ) }
  have hj : ∀ (c : B) χ a, (c • j χ).ofConv a = χ a • c := fun c χ a =>
    (mul_comm _ _).trans (Algebra.smul_def _ _).symm
  have e : toConv f = ∑ i ∈ s, b i • j (φ i) := WithConv.ext (LinearMap.ext fun a => by
    rw [ofConv_toConv, hf, ofConv_sum, LinearMap.sum_apply]
    simp only [hj])
  have h0 := natCast_eq_zero_of_algebra h (WithConv (A →ₗ[R] B))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, ← frobRing_apply h0, map_sum, ofConv_sum, LinearMap.sum_apply]
  simp only [frobRing_apply, smul_pow, ← map_pow, hj]

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} [hp : Fact p.Prime] {R S : Type} [CommRing R] [CommRing S]

theorem prime_smul_id_app (G : PDivGroup p R) (n : ℕ) (a : G.A n) :
    Hom.app ((p : ℤ_[p]) • 𝟙 G) n a = mulBy R _ p a := by rw [natCast_smul_id_app]

theorem eq_zero_of_prime_smul_eq_zero {G H : PDivGroup p R} {f : G ⟶ H}
    (e : (p : ℤ_[p]) • f = 0) : f = 0 := by
  have e' : ((p : ℤ_[p]) • 𝟙 G) ≫ f = ((p : ℤ_[p]) • 𝟙 G) ≫ 0 := by
    rw [Linear.smul_comp, Category.id_comp, e, Limits.comp_zero]
  refine Hom.ext (funext fun n => BialgHom.ext fun a => Test.mulP_injective G n ?_)
  obtain ⟨b, rfl⟩ := H.res_surjective n a
  rw [← res_app, ← res_app, mulP_res, mulP_res, ← prime_smul_id_app, ← prime_smul_id_app]
  exact congrArg (fun g => Hom.app g (n + 1) b) e'

variable (h : (p : R) = 0) (G : PDivGroup p R)

theorem verschiebung_app_eq_sum (n : ℕ) {ι : Type} (s : Finset ι) (φ : ι → CartierDual R (G.A n))
    (e : ι → G.A n) (hs : ∀ a, ∑ i ∈ s, φ i a • e i = a) (a : G.A n) :
    (verschiebung h G).app n a = ∑ i ∈ s, (φ i ^ p) a • (frobProj h G).app n (e i) :=
  frobTwist_ext_dual h n fun χ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [frobTwistDual_verschiebung, map_sum]
    refine (convPow_prime_apply h s φ (fun i => χ (e i)) χ.ofConv
      (fun a => by simpa only [map_sum, map_smul] using congrArg χ.ofConv (hs a).symm) a).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_smul, frobTwistDual_frobProj]

theorem relFrob_app_verschiebung_app (n : ℕ) (a : G.A n) :
    (relFrob h G).app n ((verschiebung h G).app n a) = mulBy R _ p a := by
  obtain ⟨s, hs⟩ := exists_dualSystem R (G.A n)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [verschiebung_app_eq_sum h G n s Prod.fst Prod.snd hs, map_sum]
  simp only [map_smul, relFrob_app_frobProj]
  refine (convPow_prime_apply h s Prod.fst Prod.snd LinearMap.id (fun a => (hs a).symm) a).symm.trans ?_
  exact (congrArg (fun f => f.ofConv a)
    (BialgHom.toLinearMap_convPow (toConv (BialgHom.id R (G.A n))) p)).symm

theorem relFrob_comp_verschiebung : relFrob h G ≫ verschiebung h G = (p : ℤ_[p]) • 𝟙 G :=
  Hom.ext (funext fun n => BialgHom.ext fun a =>
    (relFrob_app_verschiebung_app h G n a).trans (prime_smul_id_app G n a).symm)

theorem frobProj_app_relFrob_app (n : ℕ) (x : (frobTwist h G).A n) :
    (frobProj h G).app n ((relFrob h G).app n x) = x ^ p := by
  rw [← absFrob_app h]
  induction x using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => simp only [map_add (f := _), hx, hy]
  | h1 r a =>
    rw [map_smul, SemiBialgHom.smul_map, SemiBialgHom.smul_map, relFrob_app_frobProj, map_pow,
      absFrob_app]

theorem verschiebung_comp_relFrob :
    verschiebung h G ≫ relFrob h G = (p : ℤ_[p]) • 𝟙 (frobTwist h G) :=
  frobTwist_hom_ext h fun n a => by
    rw [prime_smul_id_app, ← SemiBialgHom.map_mulBy, ← relFrob_app_verschiebung_app h,
      frobProj_app_relFrob_app, ← map_pow, ← relFrob_app_frobProj h]
    rfl

variable {G}

theorem epi_relFrob : Epi (relFrob h G) :=
  Preadditive.epi_of_cancel_zero _ fun g e => eq_zero_of_prime_smul_eq_zero (by
    rw [← Category.id_comp g, ← Linear.smul_comp, ← verschiebung_comp_relFrob, Category.assoc, e,
      Limits.comp_zero])

theorem eq_verschiebung_of_relFrob_comp {v : frobTwist h G ⟶ G}
    (e : relFrob h G ≫ v = (p : ℤ_[p]) • 𝟙 G) : v = verschiebung h G :=
  haveI := epi_relFrob h (G := G)
  (cancel_epi _).1 (e.trans (relFrob_comp_verschiebung h G).symm)

section Naturality

variable (h' : (p : S) = 0) {σ : R →+* S} {G' : PDivGroup p S} (s : SemiHom σ G' G)

theorem SemiHom.app_relFrob (n : ℕ) (x : (PDivGroup.frobTwist h G).A n) :
    s.app n ((relFrob h G).app n x) = (relFrob h' G').app n ((s.frobTwist h h').app n x) := by
  induction x using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => simp only [map_add (f := _), hx, hy]
  | h1 r a =>
    rw [map_smul, SemiBialgHom.smul_map, SemiBialgHom.smul_map, map_smul, relFrob_app_frobProj,
      SemiHom.frobTwist_app_frobProj, relFrob_app_frobProj, map_pow]

theorem SemiHom.app_verschiebung (n : ℕ) (a : G.A n) :
    (s.frobTwist h h').app n ((verschiebung h G).app n a) =
      (verschiebung h' G').app n (s.app n a) := by
  refine Test.mulP_injective (PDivGroup.frobTwist h' G') n ?_
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [← PDivGroup.res_app, ← SemiHom.res_app, ← SemiHom.res_app, ← PDivGroup.res_app, mulP_res,
    mulP_res, ← map_mulBy,
    ← SemiBialgHom.map_mulBy (s.app _), ← relFrob_app_verschiebung_app h, s.app_relFrob h h',
    ← prime_smul_id_app, ← verschiebung_comp_relFrob]
  rfl

variable {H : PDivGroup p R}

variable (G) [Algebra R S]

end Naturality

variable (G)

theorem dualHom_verschiebung :
    dualHom _ _ (verschiebung h G) ≫ (frobTwistDual h G).hom = relFrob h G.dual :=
  frobTwist_hom_ext h fun n χ => (CartierDual.ext_apply fun a =>
    frobTwistDual_verschiebung h n χ a).trans (relFrob_app_frobProj h (G := G.dual) n χ).symm

theorem dualHom_relFrob :
    (frobTwistDual h G).hom ≫ verschiebung h G.dual = dualHom _ _ (relFrob h G) := by
  rw [← Iso.eq_inv_comp]
  refine (eq_verschiebung_of_relFrob_comp h ?_).symm
  rw [← dualHom_verschiebung, Category.assoc, Iso.hom_inv_id_assoc, ← dualHom_comp,
    relFrob_comp_verschiebung, map_smul, dualHom_id]

theorem omegaMap_relFrob : omegaMap _ _ (relFrob h G) = 0 :=
  LinearMap.ext fun w => Subtype.ext (funext fun n => by
    obtain ⟨x, hx⟩ := AugCot.d_surjective _ (w.1 n)
    rw [omegaMap_val, ← hx, cotMap_d]
    change dUnit (R := R) _ = 0
    clear hx
    induction x using frobTwist_induction h n with
    | h0 => simp only [map_zero]
    | h2 x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
    | h1 r a => rw [map_smul, relFrob_app_frobProj, dUnit, map_smul, ← dUnit, dUnit_pow_prime h, smul_zero])

theorem rigExtMap_relFrob_comp_rigOfOmega :
    rigExtMap (relFrob h G) ∘ₗ (frobTwist h G).rigOfOmega = 0 :=
  LinearMap.ext fun w => by
    rw [LinearMap.comp_apply, rigExtMap_rigOfOmega, omegaMap_relFrob, LinearMap.zero_apply, map_zero,
      LinearMap.zero_apply]

theorem verschiebung_app_eq_zero (n : ℕ) {b : G.A n} (hb : cobOne R _ b = 0) :
    (verschiebung h G).app n b = 0 :=
  frobTwist_ext_dual h n fun χ => by
    rw [frobTwistDual_verschiebung, map_zero, ← primTangent_d ⟨b, hb⟩, dUnit_pow_prime h, map_zero]

theorem vecExtMap_verschiebung : vecExtMap (verschiebung h G) = 0 :=
  LinearMap.ext fun x => ((frobTwist h G).extChar_bijective h).1 (Subtype.ext (by
    rw [extChar_vecExtMap h, verschiebung_app_eq_zero h G 1 (G.extChar h x).2, LinearMap.zero_apply,
      map_zero]
    rfl))

theorem range_rigExtMap_verschiebung_le :
    LinearMap.range (rigExtMap (verschiebung h G)) ≤ LinearMap.range (frobTwist h G).rigOfOmega := by
  rintro _ ⟨x, rfl⟩
  refine ((frobTwist h G).exact_rigOfOmega_rigToExt _).1 ?_
  rw [rigToExt_rigExtMap, vecExtMap_verschiebung, LinearMap.zero_apply]

theorem rigExtMap_relFrob_rig (x : G.RigExt) :
    rigExtMap (relFrob h G) ((frobProj h G).rig x) = (absFrob h G).rig x := by
  rw [← SemiHom.ofHom_rig]
  exact (frobProj h G).rig_rig _ _
    (fun n a => (absFrob_app h G n a).trans (relFrob_app_frobProj h n a).symm) x

section Perfect

variable {k : Type} [Field k] [CharP k p]

end Perfect

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearShortExactCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem baseChange_middle_equiv_of_exact : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (W' M' H' : Type) [AddCommGroup W'] [Module R' W'] [AddCommGroup M'] [Module R' M'] [AddCommGroup H'] [Module R' H'] (i : W →ₗ[R] M) (p : M →ₗ[R] H) (i' : W' →ₗ[R'] M') (p' : M' →ₗ[R'] H') (a : W →ₛₗ[algebraMap R R'] W') (b : M →ₛₗ[algebraMap R R'] M') (c : H →ₛₗ[algebraMap R R'] H'), Function.Surjective p → Function.Exact i p → Function.Injective i' → Function.Exact i' p' → (∀ x, b (i x) = i' (a x)) → (∀ x, p' (b x) = c (p x)) → (∃ e : R' ⊗[R] W ≃ₗ[R'] W', ∀ x, e (1 ⊗ₜ x) = a x) → (∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ x, e (1 ⊗ₜ x) = c x) → ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ x, e (1 ⊗ₜ x) = b x := by
  intro R R' _ _ _ W M H _ _ _ _ _ _ W' M' H' _ _ _ _ _ _ i p i' p' a b c hp hip hi' hip' hb hc hW hH
  obtain ⟨eW, heW⟩ := hW
  obtain ⟨eH, heH⟩ := hH
  letI : Module R M' := Module.compHom M' (algebraMap R R')
  haveI : IsScalarTower R R' M' := ⟨fun r s x => by
    show (r • s) • x = algebraMap R R' r • s • x
    rw [Algebra.smul_def, mul_smul]⟩
  let b' : M →ₗ[R] M' :=
    { toFun := b, map_add' := b.map_add, map_smul' := fun r m => b.map_smulₛₗ r m }
  let f : R' ⊗[R] M →ₗ[R'] M' := b'.liftBaseChange R'
  have hf1 : ∀ x, f (1 ⊗ₜ x) = b x := by
    intro x; simp [f, b']
  have hfp : ∀ s, p' (f s) = eH (LinearMap.baseChange R' p s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      have h1 : (r ⊗ₜ[R] m : R' ⊗[R] M) = r • (1 ⊗ₜ m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]; simp only [map_smul, hf1, LinearMap.baseChange_tmul, heH, hc]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hfi : ∀ u, f (LinearMap.baseChange R' i u) = i' (eW u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r w =>
      have h1 : (r ⊗ₜ[R] w : R' ⊗[R] W) = r • (1 ⊗ₜ w) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]; simp only [map_smul, hf1, LinearMap.baseChange_tmul, heW, hb]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hex : Function.Exact (LinearMap.baseChange R' i) (LinearMap.baseChange R' p) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    first | exact lTensor_exact R' hip hp | exact LinearMap.lTensor_exact R' hip hp
  have hsurj : Function.Surjective (LinearMap.baseChange R' p) := by
    rw [LinearMap.baseChange_eq_ltensor]; exact LinearMap.lTensor_surjective R' hp
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    have h0 : LinearMap.baseChange R' p s = 0 := by
      have := hfp s
      rw [hs, map_zero] at this
      exact (LinearEquiv.map_eq_zero_iff eH).1 this.symm
    obtain ⟨u, rfl⟩ := (hex s).1 h0
    have h2 : i' (eW u) = 0 := by rw [← hfi u, hs]
    have h3 : eW u = 0 := hi' (by rw [h2, map_zero])
    rw [(LinearEquiv.map_eq_zero_iff eW).1 h3, map_zero]
  have hsur : Function.Surjective f := by
    intro m'
    obtain ⟨s, hs⟩ := hsurj (eH.symm (p' m'))
    have h0 : p' (m' - f s) = 0 := by
      rw [map_sub, hfp, hs, LinearEquiv.apply_symm_apply, sub_self]
    obtain ⟨w', hw'⟩ := (hip' _).1 h0
    refine ⟨s + LinearMap.baseChange R' i (eW.symm w'), ?_⟩
    rw [map_add (f := _), hfi, LinearEquiv.apply_symm_apply, hw', add_sub_cancel]
  have hbij : Function.Bijective f := ⟨hinj, hsur⟩
  exact ⟨LinearEquiv.ofBijective f hbij, fun x => hf1 x⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableUnderGeneralizationSectionComponents
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem stableUnderGeneralization_sectionComponents :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ →
      StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  intro X S f e hf hef x x' hxx' hx
  obtain ⟨V, _, _, _, g, hgc, hgb⟩ := GlobalTheory.T.exists_valuationRing_dominating_specialization X x' x hxx'
  set p : Spec (CommRingCat.of V) ⟶ S := g ≫ f with hp
  have hpb : IsPullback (pullback.fst f p) (pullback.snd f p) f p := IsPullback.of_hasPullback f p
  let σ : Spec (CommRingCat.of V) ⟶ pullback f p := pullback.lift g (𝟙 _) (by simp [hp])
  let e' : Spec (CommRingCat.of V) ⟶ pullback f p :=
    pullback.lift (p ≫ e) (𝟙 _) (by simp [Category.assoc, hef])
  have hσf : σ ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have hσq : σ ≫ pullback.fst f p = g := pullback.lift_fst _ _ _
  have he'f : e' ≫ pullback.snd f p = 𝟙 _ := pullback.lift_snd _ _ _
  have he'q : e' ≫ pullback.fst f p = p ≫ e := pullback.lift_fst _ _ _
  haveI : Smooth f := hf
  have hf' : Smooth (pullback.snd f p) := inferInstance
  have key := _root_.GlobalTheory.sectionComponents_preimage_of_isPullback X S (pullback f p) (Spec (CommRingCat.of V)) f (pullback.snd f p) p
    (pullback.fst f p) e e' hf hpb hef he'f he'q
  have hc : σ (IsLocalRing.closedPoint V) ∈ {y : ↥(pullback f p) | y ∈ connectedComponentIn
      (pullback.snd f p ⁻¹' {pullback.snd f p y}) (e' (pullback.snd f p y))} := by
    rw [← key]
    rw [Set.mem_preimage]
    have h1 : (pullback.fst f p) (σ (IsLocalRing.closedPoint V)) = x := by
      rw [← hgc, ← hσq]
      rfl
    rw [h1]
    exact hx
  have hb := _root_.GlobalTheory.section_mem_component_generic_of_closed V (pullback f p) (pullback.snd f p) e' σ hf' he'f hσf hc
  rw [← key] at hb
  have : (pullback.fst f p) (σ (⊥ : PrimeSpectrum V)) = x' := by
    rw [← hgb, ← hσq]
    rfl
  rw [← this]
  exact hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUnique
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TwPairUniq

theorem main : ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
    ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨hI, -, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i
  obtain ⟨hJ, hJflat, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q j
  have hT : IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) :=
    GlobalTheory.T.isTateTwistResolution_tensor_flat q i j (i + j) rfl _ _ hI hJ hJflat τ hτ
  obtain ⟨huniv, -, hext⟩ := GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ
  obtain ⟨-, -, hK⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q (i + j)
  obtain ⟨⟨u, hu⟩, huniq⟩ := hK _ hT
  refine ⟨?_, ?_⟩
  · obtain ⟨ν, hν⟩ := hext u
    show IsTwPair (pick IsTwPair)
    refine pick_spec ⟨ν, fun U ζ => ?_⟩
    exact (hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).symm.trans (hu U ζ)
  · intro k hk μ ν hμ hν E n m w h
    subst hk
    obtain ⟨uμ, huμ, -⟩ := huniv μ (𝟙 _) (𝟙 _)
    obtain ⟨uν, huν, -⟩ := huniv ν (𝟙 _) (𝟙 _)
    have hom := huniq uμ uν (fun U ζ =>
      (huμ U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).trans ((hμ U ζ).trans ((hν U ζ).symm.trans
        (huν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).symm)))
    obtain ⟨hid, -, -, -, hhtp⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)
    have key : ∀ (π : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))) (v : T ⟶ res _ (tw q (i + j))),
        τ.Compat π (𝟙 _) (𝟙 _) v → ∀ a b, π.cup E h a b = cpush _ v w (τ.cup E h a b) := by
      intro π v hc a b
      rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ π (𝟙 _) (𝟙 _) v hc E h a b, (hid _ _ n a).2, (hid _ _ m b).2]
    refine AddMonoidHom.ext fun a => AddMonoidHom.ext fun b => ?_
    rw [key μ uμ huμ, key ν uν huν, (hhtp uμ uν hom _ w).2]

end GlobalTheory.EtC.TwPairUniq
end

