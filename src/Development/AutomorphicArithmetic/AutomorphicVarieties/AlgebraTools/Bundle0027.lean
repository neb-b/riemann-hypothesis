module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FlatnessPrecompleteProducts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplModfree
section
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem mult_operator_shifts_twist {Λ R B M : Type} [CommRing Λ] [CommRing R] [Algebra Λ R]
    [AddCommGroup B] [Module R B] [Module Λ B] [IsScalarTower Λ R B]
    [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M]
    [Module.Flat R B] [Module.Flat Λ M] : Module.Flat Λ (TensorProduct R B M) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor R M f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have h2 : Function.Injective
      (LinearMap.lTensor B (TensorProduct.AlgebraTensorModule.lTensor R M f)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ h1
  have h3 : ∀ x, TensorProduct.AlgebraTensorModule.assoc Λ R R B M N'
        (LinearMap.lTensor (TensorProduct R B M) f x)
      = LinearMap.lTensor B (TensorProduct.AlgebraTensorModule.lTensor R M f)
        (TensorProduct.AlgebraTensorModule.assoc Λ R R B M N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul y n =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add (f := _), hx, hy]
      | tmul b m => simp
  intro x y hxy
  apply (TensorProduct.AlgebraTensorModule.assoc Λ R R B M N).injective
  apply h2
  rw [← h3, ← h3, hxy]

theorem UpperTheory.V.AlgebraTools.IsCplAt.finite_free_baseChange :
    ∀ (Λ R : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [IsNoetherianRing R] [Algebra Λ R]
      (p : Ideal Λ) (q : Ideal R) (L B : Type) [CommRing L] [IsLocalRing L] [CommRing B] [IsLocalRing B]
      [Algebra Λ L] [Algebra R B] [Algebra L B] [Algebra Λ B] [IsScalarTower Λ R B] [IsScalarTower Λ L B]
      (M : Type) [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M] [Module.Finite Λ M] [Module.Flat Λ M],
      IsCplAt Λ p L → IsCplAt R q B → q.comap (algebraMap Λ R) = p →
      Module.Finite L (TensorProduct R B M) ∧ Module.Free L (TensorProduct R B M) :=
  _root_.UpperTheory.Reformulated.B.FlatnessPrecompleteProducts.finite_free_baseChange
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetKerIndep
section
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.generic_kernel_monotone
    (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι]
    (z : Matrix ι ι P) (m : ι → P)
    (h : CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m)) (c d : ι) :
    genKer z m c ≤ genKer z m d := by
  classical
  intro f hf
  haveI hQ : (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).IsPrime :=
    isPrime_map_C (ι := ι) (maximalIdeal P)
  set Q : Ideal (MvPolynomial ι P) := Ideal.map MvPolynomial.C (maximalIdeal P) with hQdef
  let L := Localization.AtPrime Q
  let J : Ideal L := Ideal.map (algebraMap (MvPolynomial ι P) L) (chartIdeal z m d)
  haveI hJ : J.IsPrime := chartIdeal_localization_isPrime P ι z m h d Q le_rfl
  haveI : IsLocalRing (L ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  let ψ : MvPolynomial ι P →+* L ⧸ J := (Ideal.Quotient.mk J).comp (algebraMap (MvPolynomial ι P) L)
  let φ : P →+* L ⧸ J := ψ.comp MvPolynomial.C
  have hJle : J ≤ maximalIdeal L := IsLocalRing.le_maximalIdeal hJ.ne_top
  have hψ : ∀ g ∈ chartIdeal z m d, ψ g = 0 := fun g hg =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)
  haveI : IsLocalHom φ := by
    constructor
    intro p hp
    by_contra hpu
    have hpm : p ∈ maximalIdeal P := (IsLocalRing.mem_maximalIdeal p).2 hpu
    have hC : (MvPolynomial.C p : MvPolynomial ι P) ∈ Q := Ideal.mem_map_of_mem _ hpm
    have hL : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) ∈ maximalIdeal L :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q _).2 hC
    obtain ⟨u, hu⟩ := hp
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑(u⁻¹) : L ⧸ J)
    have h1 : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) * y - 1 ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hy]
      have hu' : Ideal.Quotient.mk J (algebraMap (MvPolynomial ι P) L (MvPolynomial.C p)) = ↑u :=
        hu.symm
      rw [hu', Units.mul_inv, sub_self]
    have h3 : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) * y ∈ maximalIdeal L :=
      Ideal.mul_mem_right _ _ hL
    have h4 : (1 : L) ∈ maximalIdeal L := by
      have h5 := Ideal.sub_mem _ h3 (hJle h1)
      simpa using h5
    exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).2 h4)
  let l : ι → L ⧸ J := fun j => ψ (lam P d j)
  have hl : l d = 1 := by
    show ψ (lam P d d) = 1
    simp [lam]
  have hmul : (z.map φ).mulVec l = 0 := by
    funext i
    have hmem : (z.map MvPolynomial.C).mulVec (lam P d) i ∈ chartIdeal z m d :=
      Ideal.subset_span ⟨Sum.inl i, rfl⟩
    have h0 := hψ _ hmem
    rw [RingHom.map_mulVec, Matrix.map_map] at h0
    exact h0
  have hm : ∀ j, φ (m j) = l j * φ (m d) := by
    intro j
    by_cases hj : j = d
    · subst hj
      rw [hl, one_mul]
    · have hmem : MvPolynomial.C (m j) - lam P d j * MvPolynomial.C (m d) ∈ chartIdeal z m d :=
        Ideal.subset_span ⟨Sum.inr ⟨j, hj⟩, rfl⟩
      have h0 := hψ _ hmem
      rw [map_sub, map_mul, sub_eq_zero] at h0
      exact h0
  have hlamc : lam P d c ∉ Q := by
    rw [hQdef, MvPolynomial.mem_map_C_iff]
    intro hall
    by_cases hcd : c = d
    · have h0 := hall 0
      rw [show lam P d c = 1 from if_pos hcd, MvPolynomial.coeff_zero_one] at h0
      exact (IsLocalRing.maximalIdeal.isMaximal P).ne_top ((Ideal.eq_top_iff_one _).2 h0)
    · have h0 := hall (Finsupp.single c 1)
      rw [show lam P d c = MvPolynomial.X c from if_neg hcd, MvPolynomial.coeff_X, if_pos rfl] at h0
      exact (IsLocalRing.maximalIdeal.isMaximal P).ne_top ((Ideal.eq_top_iff_one _).2 h0)
  have hunitL : IsUnit (algebraMap (MvPolynomial ι P) L (lam P d c)) :=
    IsLocalization.map_units L (⟨lam P d c, hlamc⟩ : Q.primeCompl)
  have hunit : IsUnit (l c) := hunitL.map (Ideal.Quotient.mk J)
  set w : L ⧸ J := ↑hunit.unit⁻¹ with hwdef
  have hw : w * l c = 1 := hunit.val_inv_mul
  let l' : ι → L ⧸ J := fun j => w * l j
  have hl' : l' c = 1 := hw
  have hmul' : (z.map φ).mulVec l' = 0 := by
    funext i
    have h7 := congrFun hmul i
    simp only [l', Matrix.mulVec, dotProduct, Pi.zero_apply] at h7 ⊢
    simp_rw [mul_left_comm _ w]
    rw [← Finset.mul_sum, h7, mul_zero]
  have hm' : ∀ j, φ (m j) = l' j * φ (m c) := by
    intro j
    show φ (m j) = w * l j * φ (m c)
    rw [hm c, hm j]
    calc l j * φ (m d) = l j * φ (m d) * (w * l c) := by rw [hw, mul_one]
      _ = w * l j * (l c * φ (m d)) := by ring
  have hk := genKer_le_ker P ι z m h c (L ⧸ J) φ l' hl' hmul' hm' hf
  rw [RingHom.mem_ker] at hk
  have hfJ : algebraMap (MvPolynomial ι P) L (MvPolynomial.C f) ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.1 hk
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl L).1 hfJ
  simp only at hx
  rw [← map_mul, IsLocalization.eq_iff_exists Q.primeCompl L] at hx
  obtain ⟨⟨t, ht⟩, htx⟩ := hx
  simp only at htx
  refine ⟨t * s, ?_, ?_⟩
  · exact Q.primeCompl.mul_mem ht hs
  · have h6 : t * s * MvPolynomial.C f = t * a := by rw [← htx]; ring
    rw [h6]
    exact Ideal.mul_mem_left _ _ ha

theorem UpperTheory.V.AlgebraTools.genKer_eq :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ c d : ι, genKer z m c = genKer z m d := by
  intro P _ _ ι _ _ z m h c d
  exact le_antisymm (generic_kernel_monotone P ι z m h c d) (generic_kernel_monotone P ι z m h d c)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkSum
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkSum :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) R), IsDual a c →
      ∑ i, b.th (a i) * b.one * b.th (c i) = b.th (NN n q) := by
  intro R _ _ n q H _ _ b hb ι _ a c hd
  classical
  let S : H → Prop := fun h => ∃ e : Perm (Fin n) → MvPolynomial (Fin n) R,
    ∑ u, b.th (e u) * b.T u = h
  have S_zero : S 0 := ⟨0, by simp⟩
  have S_add : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ + h₂) := by
    rintro h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
    refine ⟨e₁ + e₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [add_mul]
  have S_sub : ∀ h₁ h₂, S h₁ → S h₂ → S (h₁ - h₂) := by
    rintro h₁ h₂ ⟨e₁, rfl⟩ ⟨e₂, rfl⟩
    refine ⟨e₁ - e₂, ?_⟩
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [sub_mul]
  have S_sum : ∀ {κ : Type} (s : Finset κ) (f : κ → H), (∀ k ∈ s, S (f k)) → S (∑ k ∈ s, f k) :=
    fun s f hf => Finset.sum_induction f S S_add S_zero hf
  have S_th : ∀ x, S (b.th x) := by
    intro x
    refine ⟨fun u => if u = 1 then x else 0, ?_⟩
    rw [Finset.sum_eq_single (1 : Perm (Fin n))]
    · simp [b.T_one]
    · intro u _ hu
      simp [hu]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have S_T : ∀ w h, S h → S (b.T w * h) := by
    rintro w h ⟨e, rfl⟩
    obtain ⟨e', he'⟩ := UpperTheory.V.AlgebraTools.hkSpan R n q H b w e
    exact ⟨e', he'.symm⟩
  have S_thmul : ∀ x h, S h → S (b.th x * h) := by
    rintro x h ⟨e, rfl⟩
    refine ⟨fun u => x * e u, ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul, mul_assoc]
  have hE : S (∑ i, b.th (a i) * b.one * b.th (c i)) := by
    refine S_sum _ _ fun i _ => ?_
    rw [mul_assoc, Bern.one, Finset.sum_mul]
    exact S_thmul _ _ (S_sum _ _ fun w _ => S_T _ _ (S_th _))
  obtain ⟨e, he⟩ := S_sub _ _ hE (S_th (NN n q))
  have hx : ∀ x, (∑ i, b.th (a i) * b.one * b.th (c i)) * b.th x * b.one
      = b.th (NN n q * x) * b.one := by
    intro x
    rw [Finset.sum_mul, Finset.sum_mul]
    have step : ∀ i, b.th (a i) * b.one * b.th (c i) * b.th x * b.one
        = b.th (a i * dd (c i * (NN n q * x))) * b.one := by
      intro i
      have hs := UpperTheory.V.AlgebraTools.hkSandwich R n q H b hb (c i * x)
      calc b.th (a i) * b.one * b.th (c i) * b.th x * b.one
          = b.th (a i) * (b.one * b.th (c i * x) * b.one) := by
            rw [map_mul]
            simp only [mul_assoc]
        _ = b.th (a i) * (b.th (dd (NN n q * (c i * x))) * b.one) := by rw [hs]
        _ = b.th (a i * dd (c i * (NN n q * x))) * b.one := by
            rw [map_mul, mul_left_comm (NN n q) (c i) x, mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl fun i _ => step i, ← Finset.sum_mul, ← map_sum,
      (UpperTheory.V.AlgebraTools.hkDualExp R n ι a c hd (NN n q * x)).1]
  have he0 := UpperTheory.V.AlgebraTools.hkFaith R n q H b hb e (fun x => by
    rw [he, sub_mul, sub_mul, hx x, ← map_mul, sub_self])
  rw [he0] at he
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at he
  exact (sub_eq_zero.mp he.symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLeviMul
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {G : Type} [Group G]

private theorem mem_stab (I : Subgroup G) (z g : G) :
    g ∈ MulAction.stabilizer G (z : G ⧸ I) ↔ z⁻¹ * g * z ∈ I := by
  rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_coe, eq_comm, QuotientGroup.eq, smul_eq_mul, mul_assoc]

private theorem ncard_orb (I K : Subgroup G) (q : G ⧸ I) :
    (MulAction.orbit K q).ncard = (MulAction.stabilizer G q).relIndex K := by
  rw [← MulAction.index_stabilizer]
  rfl

private theorem count (I : Subgroup G) (x y : G)
    (hA : ∀ g ∈ I, (x * y)⁻¹ * g * (x * y) ∈ I → x⁻¹ * g * x ∈ I)
    (hB : ∀ b ∈ I, ∃ b' ∈ I, x * b' * x⁻¹ ∈ I ∧ y⁻¹ * (b'⁻¹ * b) * y ∈ I) :
    (MulAction.orbit I ((x * y : G) : G ⧸ I)).ncard =
      (MulAction.orbit I (x : G ⧸ I)).ncard * (MulAction.orbit I (y : G ⧸ I)).ncard := by
  have h1 : MulAction.orbit (MulAction.stabilizer G (x : G ⧸ I) ⊓ I : Subgroup G) ((x * y : G) : G ⧸ I) =
      (fun q : G ⧸ I => x • q) '' MulAction.orbit I (y : G ⧸ I) := by
    ext q
    constructor
    · rintro ⟨⟨g, hg, hg'⟩, rfl⟩
      refine ⟨_, ⟨⟨x⁻¹ * g * x, (mem_stab I x g).1 hg⟩, rfl⟩, ?_⟩
      show ((x * (x⁻¹ * g * x * y) : G) : G ⧸ I) = ((g * (x * y) : G) : G ⧸ I)
      congr 1
      group
    · rintro ⟨_, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
      obtain ⟨b', hb', h1, h2⟩ := hB b hb
      refine ⟨⟨x * b' * x⁻¹, (mem_stab I x _).2 (by simpa [mul_assoc] using hb'), h1⟩, ?_⟩
      show ((x * b' * x⁻¹ * (x * y) : G) : G ⧸ I) = ((x * (b * y) : G) : G ⧸ I)
      rw [QuotientGroup.eq]
      convert h2 using 1
      group
  have h2 := ncard_orb I (MulAction.stabilizer G (x : G ⧸ I) ⊓ I) ((x * y : G) : G ⧸ I)
  rw [h1, Set.ncard_image_of_injective _ (MulAction.injective x)] at h2
  rw [h2, ncard_orb, ncard_orb, mul_comm, ← Subgroup.inf_relIndex_right (MulAction.stabilizer G (x : G ⧸ I)),
    ← Subgroup.inf_relIndex_right _ (MulAction.stabilizer G (x : G ⧸ I) ⊓ I),
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right inf_le_right,
    ← Subgroup.inf_relIndex_right (MulAction.stabilizer G ((x * y : G) : G ⧸ I))]
  congr 1
  refine le_antisymm (fun g hg => ⟨hg.1, ?_, hg.2⟩) fun g hg => ⟨hg.1, hg.2.2⟩
  exact (mem_stab I x g).2 (hA g hg.2 ((mem_stab I _ g).1 hg.1))

private theorem split_mem {I : Subgroup G} (F : LeviFact I) {u j : G} (hu : u ∈ F.Uf) (hj : j ∈ F.Mf) (h : u * j ∈ I) :
    u ∈ I ∧ j ∈ I := by
  obtain ⟨u', hu', j', hj', l, hl, e⟩ := F.fact _ h
  have := F.uniq (j'⁻¹ * (u'⁻¹ * u) * j'⁻¹⁻¹) (F.M_U _ (inv_mem hj'.1) _ (mul_mem (inv_mem hu'.1) hu)) (j'⁻¹ * j)
    (mul_mem (inv_mem hj'.1) hj) l⁻¹ (inv_mem hl.1) (by
      calc _ = j'⁻¹ * u'⁻¹ * (u * j) * l⁻¹ := by group
        _ = 1 := by rw [e]; group)
  have h2 : j = j' := (inv_mul_eq_one.1 this.2).symm
  have h3 : j ∈ I := h2 ▸ hj'.2
  exact ⟨by simpa using mul_mem h (inv_mem h3), h3⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.leviMul :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (F : LeviFact I) (m m' : G), HeckePair I → F.Pos m → F.Pos m' → (F.NormJ m ∨ F.NormJ m') → F.Pos (m * m') ∧ hk ρ I m * hk ρ I m' = hk ρ I (m * m') := by
  intro A G M _ _ _ _ ρ I F m m' hI hm hm' hN
  have hP : F.Pos (m * m') := by
    refine ⟨mul_mem hm.1 hm'.1, fun u hu => ?_, fun l hl => ?_⟩
    · have := hm.2.1 _ ⟨F.M_U _ hm'.1 u hu.1, hm'.2.1 u hu⟩
      convert this using 1
      group
    · have := hm'.2.2 (m⁻¹ * l * m) ⟨by simpa using F.M_L _ (inv_mem hm.1) l hl.1, hm.2.2 l hl⟩
      convert this using 1
      group
  have hB : ∀ b ∈ I, ∃ b' ∈ I, m * b' * m⁻¹ ∈ I ∧ m'⁻¹ * (b'⁻¹ * b) * m' ∈ I := by
    intro b hb
    obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact b hb
    rcases hN with hN | hN
    · refine ⟨u * j, mul_mem hu.2 hj.2, ?_, ?_⟩
      · convert mul_mem (hm.2.1 u hu) (hN j hj).1 using 1
        group
      · convert hm'.2.2 l hl using 1
        group
    · refine ⟨u, hu.2, hm.2.1 u hu, ?_⟩
      convert mul_mem (hN j hj).2 (hm'.2.2 l hl) using 1
      group
  have hA : ∀ g ∈ I, (m * m')⁻¹ * g * (m * m') ∈ I → m⁻¹ * g * m ∈ I := by
    intro g hg h
    obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact g hg
    have hU : (m * m')⁻¹ * u * (m * m') ∈ F.Uf := by
      simpa using F.M_U _ (inv_mem hP.1) u hu.1
    have hJ : (m * m')⁻¹ * j * (m * m') ∈ F.Mf := mul_mem (mul_mem (inv_mem hP.1) hj.1) hP.1
    obtain ⟨h1, h2⟩ := split_mem F hU hJ (by
      convert mul_mem h (inv_mem (hP.2.2 l hl)) using 1
      group)
    have h3 : m⁻¹ * u * m ∈ I := by
      convert hm'.2.1 _ ⟨hU, h1⟩ using 1
      group
    have h4 : m⁻¹ * j * m ∈ I := by
      rcases hN with hN | hN
      · exact (hN j hj).2
      · convert (hN _ ⟨hJ, h2⟩).1 using 1
        group
    convert mul_mem (mul_mem h3 h4) (hm.2.2 l hl) using 1
    group
  refine ⟨hP, hkMul A G M ρ I m m' hI (fun b hb => ?_) (count I m m' hA hB)⟩
  obtain ⟨b', -, h1, h2⟩ := hB b hb
  exact ⟨_, h1, _, h2, by group⟩
end

