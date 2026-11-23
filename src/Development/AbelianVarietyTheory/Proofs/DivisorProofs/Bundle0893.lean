module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0728
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyDerivCompNeg
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.Parity

theorem polyDeriv_comp_neg {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (P : MvPolynomial σ ℂ) (d : ℕ)
    (hP : P.IsHomogeneous d) (u : σ → W) (F : W → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => F (-z)) 0 = (-1) ^ d * ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : Multiset.card (Finsupp.toMultiset m) = d := by
    rw [Finsupp.card_toMultiset, ← hP (MvPolynomial.mem_support_iff.1 hm), Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  have h := (ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W).iteratedFDerivWithin_comp_right F uniqueDiffOn_univ
    (x := 0) (Set.mem_univ _) (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have e : (fun z => F (-z)) = F ∘ (ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W) := rfl
  rw [e, h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  have e2 : ∀ t : W, ((ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W) : W →L[ℂ] W) t = (-1 : ℂ) • t := fun t => by simp
  simp only [e2]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← hd]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

def reflTF (n g : ℕ) : TF n g ≃+ TF n g where
  toFun φ := fun x => φ (-x)
  invFun φ := fun x => φ (-x)
  left_inv φ := by funext x; simp
  right_inv φ := by funext x; simp
  map_add' _ _ := rfl

theorem reflTF_smul (a : ℂ) (φ : TF n g) : reflTF n g (a • φ) = a • reflTF n g φ := rfl

theorem isSB_reflTF {φ : TF n g} (h : GlobalTheory.SW.IsSB φ) : GlobalTheory.SW.IsSB (reflTF n g φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx k i => ?_, fun x y hy => ?_⟩
  · have := (h1 (-x) hx k i).neg
    simpa using this
  · have := h2 (-x) (-y) fun k i => (hy k i).neg
    change φ _ = φ _
    rw [← this, neg_add, smul_neg]

theorem thA_reflTF (φ : TF n g) (x : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (reflTF n g φ) x z = thA X bas idx φ x (-z) := by
  unfold thA thS
  congr 1
  · simp only [Pi.neg_apply, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  · rw [← (Equiv.neg (Matrix (Fin n) (Fin g) ℚ)).tsum_eq]
    refine tsum_congr fun y => ?_
    have e : ∀ k, qv ((-y) k) = -qv (y k) := fun k => by
      funext i
      simp [qv]
    have e' : reflTF n g φ (-y) = φ y := by
      change φ (- -y) = φ y
      rw [neg_neg]
    simp only [Equiv.neg_apply, e, e', Pi.neg_apply, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

theorem reflTF_heisG (hs : IsSympl X bas) (y : Matrix (Fin n) (Fin r) E) (φ : TF n g) :
    reflTF n g (heisG X bas y φ) = heisG X bas (-y) (reflTF n g φ) := by
  have e : ∀ k, crd X bas ((-y) k) = -crd X bas (y k) := fun k => by
    have := crd_smul hs (-1) (y k)
    rw [neg_one_smul, neg_one_smul] at this
    exact this
  funext x
  change heisS _ _ φ (-x) = φ _ * _
  unfold heisS
  congr 2
  · ext k i
    simp [e]
    ring
  · congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [e, dotProduct]

theorem EF_neg_smul_neg (w : E) (u : Fin r → E) : EF X (-u) (w • -u) = EF X u (w • u) := by
  change EFBil X _ _ = EFBil X _ _
  simp

theorem epsW_neg (w : E) (y : Matrix (Fin n) (Fin r) E) : epsW X w (-y) = epsW X w y := by
  have e : ∀ k, (-y) k = -(y k) := fun _ => rfl
  simp only [epsW, e, EF_neg_smul_neg]

theorem reflTF_projA (hs : IsSympl X bas) (w : E) (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) {φ : TF n g}
    (hφ : reflTF n g φ = φ) : reflTF n g (projA X bas w A φ) = projA X bas w A φ := by
  unfold projA
  rw [reflTF_smul]
  congr 1
  have hm : Set.MapsTo (reflTF n g) ((fun y => epsW X w y • heisG X bas y φ) '' A)
      ((fun y => epsW X w y • heisG X bas y φ) '' A) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨-y, A.neg_mem hy, by simp only [reflTF_smul, reflTF_heisG hs, hφ, epsW_neg]⟩
  have hi : ∀ ψ, reflTF n g (reflTF n g ψ) = ψ := (reflTF n g).left_inv
  rw [AddEquiv.map_finsum]
  simp only [AddEquiv.map_finsum]
  exact finsum_mem_eq_of_bijOn (reflTF n g)
    ⟨hm, (reflTF n g).injective.injOn, fun ψ hψ => ⟨_, hm hψ, hi ψ⟩⟩ fun _ _ => rfl

theorem isTheta1_neg {w : E} {x : Frame X.Ψ r} {L : Lt E r} {θ : (Fin g → ℂ) → ℂ}
    (h : IsTheta1 X bas idx w x L θ) : IsTheta1 X bas idx w x L fun z => θ (-z) := by
  refine ⟨h.1.comp differentiable_id.neg, fun v hv => ?_⟩
  funext z
  have := congrFun (h.2 (-v) (L.neg_mem hv)) (-z)
  have e : pv X idx x (-v) = -pv X idx x v := by
    unfold pv
    rw [per_neg]
    rfl
  simp only [Pi.smul_apply, fock, eps1, EF_neg_smul_neg, e] at this ⊢
  rw [← this, smul_neg, ← neg_add, ← neg_add]
  simp only [hx, mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg, neg_neg]

theorem isTheta1_update (hs : IsSympl X bas) (hn : Even n) {w : E} {L : Lt E r} {v : TF n g}
    (hv : IsVac X bas w (tens (stdL E n) L) v) {x : Frame X.Ψ r} (hd : x ∈ X.dom) (z₀ : Fin n → Fin g → ℂ) (b : Fin n) :
    IsTheta1 X bas idx w x L fun t => thA X bas idx v x (Function.update z₀ b t) := by
  obtain ⟨h1, h2, h3⟩ := thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd v hv.1
  refine ⟨h2.comp (differentiable_pi.2 fun k => ?_), fun u hu => ?_⟩
  · by_cases hk : k = b
    · subst hk
      simp only [Function.update_self]
      exact differentiable_id
    · simp only [Function.update_of_ne hk]
      exact differentiable_const _
  · funext t
    set y : Matrix (Fin n) (Fin r) E := Pi.single b u with hy
    have hyb : y b = u := Pi.single_eq_same _ _
    have hyk : ∀ k, k ≠ b → y k = 0 := fun k hk => Pi.single_eq_of_ne hk _
    have hm : y ∈ tens (stdL E n) L := (TensLat.mem_tens_stdL L _).2 fun k => by
      by_cases hk : k = b
      · rw [hk, hyb]; exact hu
      · rw [hyk k hk]; exact L.zero_mem
    have hp : pv X idx x 0 = 0 := by
      unfold pv
      rw [per_zero]
      rfl
    have e1 : epsW X w y = eps1 X w u := by
      unfold epsW eps1
      rw [Finset.sum_eq_single b, hyb]
      · intro k _ hk
        rw [hyk k hk]
        change EFBil X _ _ = 0
        simp
      · simp
    have e2 := (h1 y (Function.update z₀ b t)).2
    rw [Finset.sum_eq_single b, hyb, Function.update_self] at e2
    · have e3 : (fun k => Function.update z₀ b t k + pv X idx x (y k)) = Function.update z₀ b (t + pv X idx x u) := by
        funext k
        by_cases hk : k = b
        · rw [hk, hyb, Function.update_self, Function.update_self]
        · rw [hyk k hk, hp, add_zero, Function.update_of_ne hk, Function.update_of_ne hk]
      rw [e3] at e2
      conv_rhs => rw [← hv.2.2 y hm, GlobalTheory.SW.UnAct.thA_smul]
      simp only [Pi.smul_apply, fock, e1, e2, Nat.cast_one, _root_.one_mul]
    · intro k _ hk
      rw [hyk k hk, hp]
      simp [hx]
    · simp


include idx in
theorem reflTF_vac (hs : IsSympl X bas) (hn : Even n) {w : E} (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r}
    (hL : SelfD X L) {v : TF n g} (hv : IsVac X bas w (tens (stdL E n) L) v) {x : Frame X.Ψ r} (hd : x ∈ X.dom) :
    reflTF n g v = v := by
  refine (((thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd v hv.1).2.2 _ (isSB_reflTF hv.1)).2 ?_).symm
  funext z
  rw [thA_reflTF]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [Subsingleton.elim (-z) z]
  by_cases h0 : thA X bas idx v x = 0
  · simp [h0]
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 h0
  have hθ := isTheta1_update idx hs hn hv hd z₀ ⟨0, hpos⟩
  set θ := fun t => thA X bas idx v x (Function.update z₀ ⟨0, hpos⟩ t) with hθd
  have ht : θ (z₀ ⟨0, hpos⟩) ≠ 0 := by simpa [hθd] using hz₀
  obtain ⟨a, ha⟩ := GlobalTheory.Dict.ThetaOne.exists_eq_smul_of_isTheta1 E r X g bas idx n hs hn w hw hw' L hL x hd _ θ
    (isTheta1_neg idx hθ) hθ (Function.ne_iff.2 ⟨_, ht⟩)
  have ha' : ∀ t, θ (-t) = a * θ t := congrFun ha
  have haa : a ^ 2 = 1 := by
    have := ha' (-z₀ ⟨0, hpos⟩)
    rw [neg_neg, ha'] at this
    exact mul_right_cancel₀ ht (by linear_combination -this)
  obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r X g bas idx n hs hn w hw hw' L hL v hv x hd θ hθ
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    have := hκ fun _ => z₀ ⟨0, hpos⟩
    rw [zero_mul] at this
    exact Finset.prod_ne_zero_iff.2 (fun _ _ => ht) this
  refine mul_left_cancel₀ hκ0 ?_
  rw [← hκ, ← hκ]
  obtain ⟨m, hm⟩ := hn
  have : a ^ n = 1 := by rw [hm, ← two_mul, pow_mul, haa, one_pow]
  simp only [Pi.neg_apply, ha', Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, this,
    _root_.one_mul]

theorem thP_gphi_neg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (q0 : ℕ) (hq : X.p0 + q0 = r) (w : E), IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ Λ : Formalism.L2.Pj.GenLat E n, Λ.Unimod → Λ.La.FG → ∀ (Q : Type) [Fintype Q] (c : Q → ℂ) (Y : Q → Matrix (Fin n) (Fin r) E) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (d : ℕ), P.IsHomogeneous d → ∀ x ∈ X.dom, thP X hq bas idx (gphi X bas w Λ.La L v c (fun q => -Y q)) P x = (-1) ^ d * thP X hq bas idx (gphi X bas w Λ.La L v c Y) P x := by
  intro E _ _ _ r g n X bas idx hs hn q0 hq w hw hw' L hL v hv Λ _ _ Q _ c Y P d hP x hd
  have h1 := reflTF_projA hs w (tens Λ.La L) (reflTF_vac idx hs hn hw hw' hL hv hd)
  have h2 : gphi X bas w Λ.La L v c (fun q => -Y q) = reflTF n g (gphi X bas w Λ.La L v c Y) := by
    unfold gphi
    rw [AddEquiv.map_finsum]
    simp only [reflTF_smul, reflTF_heisG hs, h1]
  unfold thP
  rw [h2, ← polyDeriv_comp_neg P d hP]
  congr 1
  funext z
  exact thA_reflTF idx _ x z

end GlobalTheory.AdTh.Parity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeIdempotentApproximationsDVRProof
section
open GlobalTheory.IsoTriv

namespace GlobalTheory.IsoTriv.PrimeIdempotent

theorem mem_pow_of_map_dvd {R V : Type} [CommRing R] [IsDedekindDomain R] [CommRing V]
    [IsDomain V] [IsDiscreteValuationRing V] (φ : R →+* V) (b a : R) (hb : φ b ≠ 0) (n : ℕ)
    (hw : (Ideal.comap φ (IsLocalRing.maximalIdeal V)).IsMaximal)
    (hbn : b ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n) (z : V) (hz : φ a = φ b * z) :
    a ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n := by
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  by_cases ha : a = 0
  · rw [ha]; exact Ideal.zero_mem _
  have hspan : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = i
    at hfac
  by_cases hi : n ≤ i
  · have h1 : a ∈ w ^ i * J := hfac ▸ Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_pow_right hi (Ideal.mul_le_inf h1).1
  exfalso
  have hJw : ¬ J ≤ w := fun h => hw.ne_top (by rw [← hJ, sup_eq_left.mpr h])
  obtain ⟨s, hsJ, hsw⟩ := Set.not_subset.mp hJw
  have hb1 : b ∈ w ^ (i + 1) := Ideal.pow_le_pow_right (by omega) hbn
  have h2 : b * s ∈ Ideal.span {a} * w := by
    rw [hfac, mul_right_comm, ← pow_succ]
    exact Ideal.mul_mem_mul hb1 hsJ
  obtain ⟨m, hm, hm'⟩ := Ideal.mem_span_singleton_mul.mp h2
  apply hsw
  have h3 : φ s = z * φ m := by
    apply mul_left_cancel₀ hb
    rw [← map_mul, ← hm', map_mul, hz, mul_assoc]
  change φ s ∈ IsLocalRing.maximalIdeal V
  rw [h3]
  exact Ideal.mul_mem_left _ _ hm

theorem epsSt : EpsSt := by
  intro R V _ _ _ _ _ φ q hq hu
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  have hq0 : q ≠ 0 := fun h => hq (by rw [h, map_zero])
  have hqw : q ∈ w := (IsLocalRing.mem_maximalIdeal _).mpr hu
  have hwp : w.IsPrime := Ideal.comap_isPrime φ _
  have hw0 : w ≠ ⊥ := fun h => hq0 (by rw [h] at hqw; exact hqw)
  have hw : w.IsMaximal := hwp.isMaximal hw0
  have hspan : Ideal.span {q} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {q})) = e
    at hfac
  have hpow : ∀ M : ℕ, Ideal.span {q ^ M} = w ^ (e * M) * J ^ M := fun M => by
    rw [← Ideal.span_singleton_pow, hfac, mul_pow, pow_mul]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ N : ℕ, ∃ y ∈ J ^ N, ∃ z, φ y = 1 + φ q ^ N * z := by
    intro N
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero N hq) hϖ
    have hco : w ^ k ⊔ J ^ N = ⊤ := Ideal.pow_sup_pow_eq_top hJ
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hco)
    have h1 : φ x ∈ Ideal.span {φ q ^ N} := by
      have h2 : φ x ∈ (Ideal.map φ w) ^ k := by
        rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem φ hx
      have h3 : φ x ∈ IsLocalRing.maximalIdeal V ^ k :=
        Ideal.pow_right_mono Ideal.map_comap_le k h2
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h3
      rwa [Ideal.span_singleton_eq_span_singleton.mpr hk]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h1
    refine ⟨y, hy, -c, ?_⟩
    have h4 : φ x + φ y = 1 := by rw [← map_add (f := _), hxy, map_one]
    rw [← h4, hc]; ring
  choose ε hεJ hε using key
  refine ⟨ε, fun N => ⟨hε N, fun M hM a ⟨z, hz⟩ => ?_⟩⟩
  have hqM : q ^ M ∈ w ^ (e * M) := by
    have h1 : q ^ M ∈ w ^ (e * M) * J ^ M := hpow M ▸ Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf h1).1
  have ha : a ∈ w ^ (e * M) :=
    mem_pow_of_map_dvd φ (q ^ M) a (by rw [map_pow]; exact pow_ne_zero M hq) _ hw hqM z
      (by rw [map_pow]; exact hz)
  rw [hpow M, mul_comm (ε N)]
  exact Ideal.mul_mem_mul ha (Ideal.pow_le_pow_right hM (hεJ N))

end GlobalTheory.IsoTriv.PrimeIdempotent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticTwistCmCurveModelDiscriminantNegPrimeCu
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LocAll

theorem modelAt_of_val {V : ValuationSubring ℂ} {F : IntermediateField ℚ ℂ} {W : WeierstrassCurve ℂ} {D D' : ℂ}
    (h : ModelAt V F W D) (hv : V.valuation D = V.valuation D') : ModelAt V F W D' := by
  obtain ⟨C, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨C, h1, h2, h3, h4, h5, h6.trans hv⟩

theorem mem_of_isIntegral (V : ValuationSubring ℂ) {y : ℂ} (hy : IsIntegral ℤ y) : y ∈ V := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := V) (K := ℂ) (hy.tower_top (A := V))
  exact hz ▸ z.2

theorem short_Δ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).Δ =
    d ^ 6 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem short_c₄ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).c₄ =
    d ^ 2 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).c₄ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

end GlobalTheory.CMModel.LocAll


open GlobalTheory.CMModel.LocAll in
theorem GlobalTheory.CMModel.twist_modelAt_all : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, ModelAt V F (shortTwist (if p % 8 = 3 then 1 else -(p : ℂ)) (-L.g₂ / 4) (-L.g₃ / 4)) (-(p : ℂ) ^ 3) := by
  intro p F L t hp h4 h3 hD hsq V
  have h27 : (27 : ℂ) ∈ F := by simpa using F.algebraMap_mem (27 : ℚ)
  have h4F : (4 : ℂ) ∈ F := by simpa using F.algebraMap_mem (4 : ℚ)
  have hg2 : -L.g₂ / 4 ∈ F := div_mem (neg_mem hD.g₂_mem) h4F
  have hg3 : -L.g₃ / 4 ∈ F := div_mem (neg_mem hD.g₃_mem) h4F
  have hpF : (p : ℂ) ∈ F := by simpa using F.algebraMap_mem (p : ℚ)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  by_cases hv : V.valuation (p : ℂ) = 1
  · have hgood : ModelAt V F ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ 1 := _root_.GlobalTheory.CMModel.modelAt_one_of_sqProd_mem p F L t hp h4 h3 hD hsq V hv
    split_ifs with h8
    · have hk := _root_.GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one V F (-L.g₂ / 4) (-L.g₃ / 4) 1 0 hg2 hg3 hgood
      have e : (4 * ((0 : ℤ) : ℂ) + 1) = 1 := by simp
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, p + 1 = 4 * m := ⟨(p + 1) / 4, by omega⟩
      have hk := _root_.GlobalTheory.CMModel.modelAt_shortTwist_four_mul_add_one V F (-L.g₂ / 4) (-L.g₃ / 4) 1 (-(m : ℤ)) hg2 hg3 hgood
      have hmC : (p : ℂ) + 1 = 4 * m := by exact_mod_cast hm
      have e : (4 * ((-(m : ℤ) : ℤ) : ℂ) + 1) = -(p : ℂ) := by push_cast; linear_combination hmC
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
  · have h6 : V.valuation (6 : ℂ) = 1 := by
      have hc : Nat.Coprime p 6 := by
        have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
        have h3' : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
        simpa using Nat.Coprime.mul_right h2 h3'
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V p 6 hc with h | h
      · exact absurd h hv
      · exact_mod_cast h
    obtain ⟨A, hAF, hA0, hA⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp h4 h3 hD V
    have hsq8 := GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp h4 h3 hD
    have hΔF : (latticeCurve L).Δ ∈ F := by
      rw [latticeCurve_Δ]
      exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem h27 (pow_mem hD.g₃_mem 2))
    obtain ⟨u, huF, hu0, hu⟩ := _root_.GlobalTheory.valuation_twelfth_power_of_cube p V F (latticeCurve L).Δ A (sqProd p L t) h4 hΔF hAF hsq
      (latticeCurve_Δ_ne_zero L) hA0 hA hsq8
    have him : (sqrtNegNat p).im ≠ 0 := by
      simp [sqrtNegNat]
      exact hp.pos.ne'
    have hj : (latticeCurve L).j ∈ V := mem_of_isIntegral V (_root_.GlobalTheory.CMModel.LatticeJInt.main L (sqrtNegNat p) hD.mul him)
    have hjΔ := GlobalTheory.j_mul_Δ (latticeCurve L)
    have hDV : -(p : ℂ) ^ 3 ∈ V := neg_mem (pow_mem (natCast_mem V p) 3)
    have hvD : V.valuation (-(p : ℂ) ^ 3) = V.valuation (p : ℂ) ^ 3 := by simp
    set d : ℂ := if p % 8 = 3 then 1 else -(p : ℂ) with hd
    show ModelAt V F ⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ (-(p : ℂ) ^ 3)
    have hjt : (latticeCurve L).j * (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).Δ =
        (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).c₄ ^ 3 := by
      rw [short_Δ, short_c₄]
      rw [show (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L from rfl]
      linear_combination d ^ 6 * hjΔ
    by_cases h8 : p % 8 = 3
    · have hd1 : d = 1 := by rw [hd, if_pos h8]
      rw [if_pos h8] at hu
      refine _root_.GlobalTheory.CMModel.modelAt_short_of_six_unit V F _ _ _ u _ hj hjt h6 huF hu0 hDV ?_
      rw [short_Δ, hvD, hd1, one_pow, one_mul]
      exact hu
    · have hdp : d = -(p : ℂ) := by rw [hd, if_neg h8]
      rw [if_neg h8] at hu
      refine _root_.GlobalTheory.CMModel.modelAt_short_of_six_unit V F _ _ _ (u * p) _ hj hjt h6 (mul_mem huF hpF) (mul_ne_zero hu0 hp0) hDV ?_
      rw [short_Δ, hvD, hdp]
      change V.valuation (u * p) ^ 12 * V.valuation (p : ℂ) ^ 3 = V.valuation ((-(p : ℂ)) ^ 6 * (latticeCurve L).Δ)
      rw [map_mul, map_mul, map_pow, Valuation.map_neg, ← hu, mul_pow]
      rw [show V.valuation (p : ℂ) ^ 9 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 3 by rw [← pow_add],
        show V.valuation (p : ℂ) ^ 12 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 6 by rw [← pow_add]]
      ac_rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatedPairsSamePolarization
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.Pair

def innerAlgEquiv (R : Type) {A : Type} [CommRing R] [Ring A] [Algebra R A] (y : Aˣ) : A ≃ₐ[R] A :=
  GlobalTheory.InnerAutomorphism.innerAut R y

theorem rel_pol_c : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G), P.Rel Q → Q.pol = P.pol ∧ Q.c = P.c := by
  intro p _ G P Q ⟨y, s, _, hβ, hγ⟩
  refine ⟨?_, ?_⟩
  · have h := minpoly.algEquiv_eq (innerAlgEquiv G.F y) (P.γ : G.C)
    simp only [pol, hγ, Units.val_mul]
    exact h
  · have hsh : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
      intro a b; simp [sh]
    have hy : ∀ X : G.C, sh G (y : G.C) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * X) = X := by
      intro X
      rw [← mul_assoc, ← hsh, Units.inv_mul, sh, map_one, MulOpposite.unop_one, one_mul]
    have core : (y : G.C) * P.γ * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * P.β * sh G y) *
        (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G P.γ * sh G y)) = (P.c : ℚ) • ((y : G.C) * P.β * sh G y) := by
      calc (y : G.C) * P.γ * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * P.β * sh G y) *
            (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G P.γ * sh G y))
          = y * (P.γ * P.β * sh G P.γ) * sh G y := by
            simp only [mul_assoc, Units.inv_mul_cancel_left, hy]
        _ = _ := by
            rw [P.sim, ← Algebra.smul_def]
            simp only [mul_smul_comm, smul_mul_assoc]
    have key : algebraMap ℚ G.C (Q.c : ℚ) * Q.β = algebraMap ℚ G.C (P.c : ℚ) * Q.β := by
      rw [← Q.sim, hγ, hβ]
      simp only [Units.val_mul, hsh, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
      rw [core, smul_comm]
    have hinj : Function.Injective (algebraMap ℚ G.C) := (algebraMap ℚ G.C).injective
    exact Units.ext (hinj ((Units.mul_left_inj Q.β).mp key))

end GlobalTheory.LKMid.Pair
end
end

