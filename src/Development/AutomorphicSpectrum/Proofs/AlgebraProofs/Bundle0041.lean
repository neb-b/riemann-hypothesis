module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import ReciprocityTheory.DualLattices.Bundle0021
public import ReciprocityTheory.DualLattices.Bundle0015
public import ReciprocityTheory.DualLattices.PowMemCarrier
public import ReciprocityTheory.DualLattices.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0037
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ProdIccFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0035

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAugmentationTheorem
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.PolAF

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem hasLen_omAA_htd {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
    (H : HodgeTateDatum p g v R O σ cp) :
    HasLen v R (OmAA H.AA.carrier) (v (algebraMap R C (p : R)) ^ g) := by
  refine ⟨g, fun _ => (p : R), ⟨?_⟩, by simp⟩
  exact (Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans
    ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p g))

theorem mem_afLat_of_cong {p : ℕ} [Fact p.Prime] {g : ℕ} [Algebra ℤ_[p] R]
    (M : Submodule R (Nb p g → C)) (l : Ix g → R) (f : Nb p g → C) (hf : f ∈ M)
    (h : ∀ t : TT p g, ∃ r : R, algebraMap R C (∑ i, l i * algebraMap ℤ_[p] R (t i)) -
      f (red p g t) = algebraMap R C (p * r)) : l ∈ afLat p M := by
  refine ⟨f, hf, fun x => ?_⟩
  obtain ⟨r, hr⟩ := h (fun i => ((x i).val : ℤ_[p]))
  have hred : red p g (fun i => ((x i).val : ℤ_[p])) = x := by
    funext i; simp [red]
  have hsum : (∑ i, l i * algebraMap ℤ_[p] R (((x i).val : ℕ) : ℤ_[p])) =
      ∑ i, l i * ((x i).val : R) := by
    exact Finset.sum_congr rfl fun i _ => by rw [map_natCast]
  rw [hred, hsum] at hr
  have hx : f x - algebraMap R C (∑ i, l i * ((x i).val : R)) = -(algebraMap R C (p * r)) := by
    rw [← hr]; ring
  show _ ∈ Submodule.span R {(p : C)}
  rw [hx, Submodule.mem_span_singleton]
  refine ⟨-r, ?_⟩
  rw [Algebra.smul_def, map_mul, map_neg, map_natCast]
  ring

theorem rows_mem_afLat {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
    (H : HodgeTateDatum p g v R O σ cp) (k : Ix g) :
    Matrix.fromRows H.Ht H.Bt k ∈ afLat p H.AA.carrier := by
  rcases k with k | k
  · obtain ⟨f, hf, h⟩ := (H.h4 k).1
    exact mem_afLat_of_cong H.AA.carrier (H.Ht k) f hf h
  · obtain ⟨f, hf, h⟩ := (H.h4 k).2
    exact mem_afLat_of_cong H.AA.carrier (H.Bt k) f hf h

theorem span_rows_integral {g : ℕ} (v : Valuation C NNReal) (hv : v.Integers R)
    (Ht Bt : Matrix (Fin g) (Ix g) R) (x : Ix g → C) :
    (∀ l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k),
      v (∑ i, algebraMap R C (l i) * x i) ≤ 1) ↔
    (∀ k, v ((Ht.map (algebraMap R C) *ᵥ x) k) ≤ 1) ∧
      ∀ k, v ((Bt.map (algebraMap R C) *ᵥ x) k) ≤ 1 := by
  constructor
  · intro h
    refine ⟨fun k => ?_, fun k => ?_⟩
    · simpa [Matrix.mulVec, dotProduct] using h _ (Submodule.subset_span ⟨Sum.inl k, rfl⟩)
    · simpa [Matrix.mulVec, dotProduct] using h _ (Submodule.subset_span ⟨Sum.inr k, rfl⟩)
  · rintro ⟨h1, h2⟩ l hl
    induction hl using Submodule.span_induction with
    | mem l hl =>
      obtain ⟨k, rfl⟩ := hl
      rcases k with k | k
      · simpa [Matrix.mulVec, dotProduct] using h1 k
      · simpa [Matrix.mulVec, dotProduct] using h2 k
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
      exact (v.map_add _ _).trans (max_le ha hb)
    | smul r a _ ha =>
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
      exact mul_le_one' (hv.map_le_one r) ha

end GlobalTheory.CompanionTheory.Ar.GR.PolAF

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem polarisedAF : PolarisedAFStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H
  intro φ AF H' hb
  classical
  have hv : v.Integers R := hS.integers
  have hp1 : v (p : C) < 1 := by simpa [map_natCast] using hS.p_lt
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hvcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h := hS.cp_val
    rw [h0, zero_pow (by omega)] at h
    exact hS.p_ne h.symm
  have hcp : cp ≠ 0 := by rintro rfl; exact hvcp (by simp)
  have hEalt : (H.E.map (algebraMap ℤ_[p] R))ᵀ = -(H.E.map (algebraMap ℤ_[p] R)) := by
    ext i j
    have h := congrFun (congrFun H.E_alternating.1 j) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    simp [Matrix.transpose_apply, Matrix.map_apply, h]
  have hEu : IsUnit (H.E.map (algebraMap ℤ_[p] R)).det := by
    have : (H.E.map (algebraMap ℤ_[p] R)).det = algebraMap ℤ_[p] R H.E.det :=
      (RingHom.map_det _ _).symm
    rw [this]; exact H.isUnit_det_E.map _
  obtain ⟨hdet, hker, himg, hcpmem⟩ :=
    GlobalTheory.T.symplectic_period_matrix_integrality C v R hv g H.Ht H.Bt _ cp hcp hEalt hEu H.form_eq_alt

  set L := Submodule.span R (Set.range fun k => Matrix.fromRows H.Ht H.Bt k) with hL
  have hLle : L ≤ AF :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact PolAF.rows_mem_afLat H k)
  have hLlen : HasLen v R ((Ix g → R) ⧸ L) (v (algebraMap R C cp) ^ g) := by
    have h := hasLen_coker_det' v R hv (Ix g) (Matrix.fromRows H.Ht H.Bt)ᵀ
    rw [Matrix.det_transpose, hdet, Matrix.range_mulVecLin] at h
    exact h

  have hkill : ∀ x : Nb p g, p • x = 0 := by intro x; ext i; simp
  obtain ⟨cA, cN, cO, -, -, -, hA, hN, hO⟩ := GlobalTheory.T.augmentation_lengths_exist p C v R hv hp1 (Nb p g) hkill H.AA
  have hcO : cO = v (algebraMap R C (p : R)) ^ g := hasLen_unique hv hO (PolAF.hasLen_omAA_htd H)
  have hdeg := u4 p C v R hv hp1 (Nb p g) hkill H.AA cN cO hN hO
  obtain ⟨hcnt, hgen⟩ := GlobalTheory.T.augmentation_length_colength_bound p C v R hv hp1 (Nb p g) hkill H.AA cA cN hA hN
  obtain ⟨eq⟩ := GlobalTheory.T.augmentation_quotient_equiv_lattice p C v R hv hp1 (Ix g) H.AA
  have hAF : HasLen v R ((Ix g → R) ⧸ AF) cA := PositivityTheory.HtPt.Rc.hasLen_of_equiv eq.symm hA
  obtain ⟨hle, hLeq⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.GR.submodule_eq_of_hasLen_eq C v R hv (Ix g) L AF hLle _ _ (pow_ne_zero _ hvcp) hLlen hAF
  have hn : Fintype.card (Nb p g) * (p - 1) ≠ 0 :=
    Nat.mul_ne_zero Fintype.card_ne_zero (by omega)
  have hOeq : cO ^ Fintype.card (Nb p g) =
      (v (algebraMap R C cp) ^ g) ^ (Fintype.card (Nb p g) * (p - 1)) := by
    rw [hcO, ← hS.cp_val, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1; ring
  have h1 : (v (algebraMap R C cp) ^ g) ^ (Fintype.card (Nb p g) * (p - 1)) ≤
      cA ^ (Fintype.card (Nb p g) * (p - 1)) := pow_le_pow_left₀ zero_le hle _
  have hAn : cA ^ (Fintype.card (Nb p g) * (p - 1)) = cN ^ 2 :=
    le_antisymm hcnt (hdeg.trans (hOeq ▸ h1))
  have hOn : cO ^ Fintype.card (Nb p g) = cN ^ 2 :=
    le_antisymm (hOeq ▸ h1.trans hAn.le) hdeg
  have hcA : cA = v (algebraMap R C cp) ^ g :=
    ((pow_left_inj₀ zero_le zero_le hn).1 (hAn.trans (hOn.symm.trans hOeq)))
  have hLAF : L = AF := hLeq hcA.symm

  have hmem : ∀ x, x ∈ H' ↔ (∀ k, v ((H.Ht.map φ *ᵥ x) k) ≤ 1) ∧
      ∀ k, v ((H.Bt.map φ *ᵥ x) k) ≤ 1 := by
    intro x
    show (∀ l ∈ AF, _) ↔ _
    rw [← hLAF]
    exact PolAF.span_rows_integral v hv H.Ht H.Bt x
  refine ⟨hLAF.symm, fun l => hLAF ▸ hcpmem l, hLAF ▸ hLlen, hcA ▸ hA, hmem, ?_, ?_,
    hgen hAn, ⟨cA, cN, cO, hA, hN, hO, hAn, hOn⟩⟩
  · intro x
    rw [← hker x, hmem]
    constructor
    · rintro ⟨⟨-, h2⟩, h0⟩; exact ⟨h0, h2⟩
    · rintro ⟨h0, h2⟩; exact ⟨⟨fun k => by rw [show H.Ht.map φ *ᵥ x = 0 from h0]; simp, h2⟩, h0⟩
  · intro w hw
    obtain ⟨x, hx1, hx2⟩ := himg w hw
    refine ⟨x, (hmem x).2 ⟨fun k => by rw [hx1]; exact hw k, fun k => by rw [show H.Bt.map φ *ᵥ x = 0 from hx2]; simp⟩, hx1⟩

end GlobalTheory.CompanionTheory.Ar.GR
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalIdeal
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
open PositivityTheory.HtPt.Rc ReciprocityTheory.PGsh.L2.SecondCohomologyLattice in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_ideal : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → (∀ χ : MulChar F R, ∃ r : NNReal, r ≠ 0 ∧ HasLen v R (OmType AA.carrier χ) r) ∧ ∀ r : ℕ → NNReal, (∀ m ∈ Finset.Icc 1 (p ^ f - 1), HasLen v R (OmType AA.carrier (σ ^ m)) (r m)) → HasLen v R (OmAA AA.carrier) (∏ m ∈ Finset.Icc 1 (p ^ f - 1), r m) := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f hf N _ _ _ _ AA hAA σ hσ
  have := hv.hom_inj.isDomain
  have hfg := fg_of_isLat AA.lat
  constructor
  · intro χ
    obtain ⟨-, -, cO, -, -, hcO0, -, -, hcO⟩ := lens p C v R hv hvp N (fun x => by
      rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]) AA
    obtain ⟨r, hr⟩ := exists_hasLen hv _ _ (eig_fg hv _ hfg χ) (sq_aug_fg hv _ hfg)
    refine ⟨r, ?_, hr⟩
    obtain ⟨s, hs0, hs⟩ := (len_ne_zero_iff hv hcO).1 hcO0
    refine (len_ne_zero_iff hv hr).2 ⟨s, hs0, fun m => ?_⟩
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have h := hs (Submodule.Quotient.mk ⟨g, eig_le_aug _ χ g.2⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h ⊢
    exact h
  · intro r hr
    obtain ⟨u, hu⟩ := exists_inv_card (F := F) hv p hvp
    have proj_mem (χ : MulChar F R) (S : Submodule R (N → C))
        (hS : FStable (F := F) S) {g : N → C} (hg : g ∈ S) : projL χ g ∈ S := by
      have heq : projL χ g = u • ∑ a : Fˣ, χ⁻¹ (a : F) • (fun x => g ((a : F) • x)) := by
        funext x
        rw [projL_apply, Pi.smul_apply, Finset.sum_apply, Algebra.smul_def, hu]
        exact congrArg _ (Finset.sum_congr rfl fun a _ => (Algebra.smul_def _ _).symm)
      rw [heq]
      exact S.smul_mem _ (S.sum_mem fun a _ => S.smul_mem _ (hS _ g hg))
    have proj_eig (χ : MulChar F R) {g : N → C} (hg : g ∈ augIdeal AA.carrier) :
        projL χ g ∈ eig AA.carrier χ := by
      rw [mem_aug] at hg
      refine ⟨proj_mem χ _ hAA hg.1, fun a x => ?_⟩
      by_cases ha : a = 0
      · rw [ha, zero_smul, MulChar.map_zero, map_zero, zero_mul, projL_apply]
        simp only [smul_zero, hg.2, mul_zero, Finset.sum_const_zero]
      · obtain ⟨a, rfl⟩ := isUnit_iff_ne_zero.2 ha
        rw [projL_apply, projL_apply, mul_left_comm, Finset.mul_sum Finset.univ _ (algebraMap R C _),
          ← Equiv.sum_comp (Equiv.mulRight a) (fun b : Fˣ => algebraMap R C (χ (a : F)) *
            (algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • x)))]
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Equiv.coe_mulRight, Units.val_mul, mul_smul, ← mul_assoc, ← map_mul, map_mul χ⁻¹,
          mul_left_comm, mul_inv_unit, mul_one]
    obtain ⟨hord, -, -, -, hsep⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hvp F f hf σ hσ
    have hn : p ^ f - 1 = Fintype.card Fˣ := by rw [Fintype.card_units, hf]
    rw [hn] at hr hord ⊢
    have hsum := sum_projL (C := C) (N := N) σ (fun a ha => by
      by_contra hne
      have := hsep a 1 (fun h => hne (Units.ext h))
      rw [ha, map_one, sub_self, map_zero, map_zero] at this
      exact zero_ne_one this)
    let Ψ : augIdeal AA.carrier →ₗ[R]
        ((i : Fin (Fintype.card Fˣ)) → OmType AA.carrier (σ ^ ((i : ℕ) + 1))) :=
      LinearMap.pi fun i => Submodule.mkQ _ ∘ₗ
        (projL (σ ^ ((i : ℕ) + 1))).restrict fun _ hg => proj_eig _ hg
    have hsurj : Function.Surjective Ψ := by
      intro y
      choose g hg using fun i => Submodule.Quotient.mk_surjective _ (y i)
      refine ⟨⟨∑ i, (g i : N → C), Submodule.sum_mem _ fun i _ => eig_le_aug _ _ (g i).2⟩, ?_⟩
      funext i
      rw [← hg i]
      refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
      show projL (σ ^ ((i : ℕ) + 1)) (∑ i, (g i : N → C)) = g i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single i, projL_self _ (g i).2]
      · intro j _ hj
        refine projL_ne (fun h => hj ?_) (g j).2
        rw [pow_succ, pow_succ] at h
        exact Fin.ext (pow_injOn_Iio_orderOf (by rw [hord]; exact j.2) (by rw [hord]; exact i.2)
          (mul_right_cancel h).symm)
      · simp
    have hker : (sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype =
        LinearMap.ker Ψ := by
      ext g
      rw [LinearMap.mem_ker, funext_iff]
      constructor
      · intro hg i
        have hstable : FStable (F := F) (sqIdeal (augIdeal AA.carrier)) :=
          fun a _ ha => sq_pull (LinearMap.lsmul F N a).toAddMonoidHom
            AA.carrier AA.carrier (hAA a) ha
        exact (Submodule.Quotient.mk_eq_zero _).2 (proj_mem _ _ hstable hg)
      · intro hg
        show (g : N → C) ∈ sqIdeal (augIdeal AA.carrier)
        rw [← hsum g]
        refine Submodule.sum_mem _ fun i _ => ?_
        have h1 : (Submodule.Quotient.mk
            (⟨projL (σ ^ ((i : ℕ) + 1)) (g : N → C), proj_eig _ g.2⟩ :
              eig AA.carrier (σ ^ ((i : ℕ) + 1))) :
            OmType AA.carrier (σ ^ ((i : ℕ) + 1))) = 0 := hg i
        rw [Submodule.Quotient.mk_eq_zero] at h1
        exact h1
    rw [prod_Icc_fin]
    exact PositivityTheory.HtPt.Rc.hasLen_of_equiv ((Submodule.quotEquivOfEq _ _ hker).trans
      (Ψ.quotKerEquivOfSurjective hsurj)) (Tot.hasLen_pi _ _ fun i =>
        hr _ (Finset.mem_Icc.2 ⟨by omega, i.2⟩))
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupCharacters
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open PositivityTheory.HtPt.Rc ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_subgroup_characters : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ (K : Submodule F N) (χ : MulChar F R) (a b c : NNReal), HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) χ) a → HasLen v R (OmType (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) χ) b → HasLen v R (OmType AA.carrier χ) c → a * b ≤ c := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f _ N _ _ _ _ AA hAA K χ a b c ha hb hc
  have hu := exists_inv_card (F := F) hv p hvp
  have hQ : FStable (F := F) (AA.carrier.comap (LinearMap.funLeft R C K.mkQ)) := by
    intro a g hg
    have hg' := hAA a _ hg
    show LinearMap.funLeft R C K.mkQ _ ∈ AA.carrier
    convert hg' using 1
    funext x
    show g (a • K.mkQ x) = g (K.mkQ (a • x))
    rw [map_smul]
  have hsq : FStable (F := F) (sqIdeal (augIdeal AA.carrier)) :=
    fun a _ hg => sq_pull (LinearMap.lsmul F N a).toAddMonoidHom _ _ (hAA a) hg
  have proj_mem {X : Type} [AddCommGroup X] [Module F X] (χ : MulChar F R)
      (S : Submodule R (X → C)) (hS : FStable (F := F) S) {g : X → C} (hg : g ∈ S) :
      projL χ g ∈ S := by
    obtain ⟨u, hu⟩ := hu
    have hproj : projL χ g = u • ∑ a : Fˣ, χ⁻¹ (a : F) • (fun x => g ((a : F) • x)) := by
      funext x
      rw [projL_apply, Pi.smul_apply, Finset.sum_apply, Algebra.smul_def, hu]
      exact congrArg _ (Finset.sum_congr rfl fun a _ => (Algebra.smul_def _ _).symm)
    rw [hproj]
    exact S.smul_mem _ (S.sum_mem fun a _ => S.smul_mem _ (hS _ g hg))
  have proj_eig {X : Type} [AddCommGroup X] [Module F X] (χ : MulChar F R)
      {M : Submodule R (X → C)} (hM : FStable (F := F) M) {g : X → C} (hg : g ∈ augIdeal M) :
      projL χ g ∈ eig M χ := by
    rw [mem_aug] at hg
    refine ⟨proj_mem χ M hM hg.1, fun a x => ?_⟩
    by_cases ha : a = 0
    · rw [ha, zero_smul, MulChar.map_zero, map_zero, zero_mul, projL_apply]
      simp only [smul_zero, hg.2, mul_zero, Finset.sum_const_zero]
    · obtain ⟨a, rfl⟩ := isUnit_iff_ne_zero.2 ha
      rw [projL_apply, projL_apply, mul_left_comm, Finset.mul_sum Finset.univ _ (algebraMap R C _),
        ← Equiv.sum_comp (Equiv.mulRight a) (fun b : Fˣ => algebraMap R C (χ (a : F)) *
          (algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • x)))]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Equiv.coe_mulRight, Units.val_mul, mul_smul, ← mul_assoc, ← map_mul, map_mul χ⁻¹,
        mul_left_comm, mul_inv_unit, mul_one]
  rw [mul_comm]
  refine len_mul_le hv (omMap χ K.mkQ (AA.carrier.comap (LinearMap.funLeft R C K.mkQ)) AA.carrier
      (fun _ hg => hg))
    (omMap χ K.subtype AA.carrier (AA.carrier.map (LinearMap.funLeft R C K.subtype))
      (fun _ hg => Submodule.mem_map_of_mem hg)) ?_ ?_ hb hc ha
  · intro y
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hgh⟩ := hh.1
    have hga : g ∈ augIdeal AA.carrier := by
      rw [mem_aug]
      refine ⟨hg, ?_⟩
      have := ((mem_aug _ _).1 (eig_le_aug _ χ hh)).2
      rw [← hgh] at this
      exact this
    refine ⟨Submodule.Quotient.mk ⟨projL χ g, proj_eig χ hAA hga⟩, ?_⟩
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    show LinearMap.funLeft R C K.subtype (projL χ g) = h
    rw [← projL_funLeft, ← projL_self χ hh, ← hgh]
  · intro x hx
    obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨q, hq, hgq⟩ := om_exact hv AA K.subtype.toAddMonoidHom K.mkQ.toAddMonoidHom
      K.mkQ_surjective Subtype.val_injective (range_subtype_eq K) g (eig_le_aug _ χ hg) hx'
    refine ⟨Submodule.Quotient.mk ⟨projL χ q, proj_eig χ hQ hq⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show g - LinearMap.funLeft R C K.mkQ (projL χ q) ∈ sqIdeal (augIdeal AA.carrier)
    have := proj_mem χ _ hsq hgq
    rw [map_sub, projL_self χ hg] at this
    rw [← projL_funLeft]
    exact this
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TensorProductHopfOrders
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.tensor_product_hopf_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), ∃ AA : HopfOrder (C := C) R (N₁ × N₂), AA.carrier = tens A₁.carrier A₂.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inl N₁ N₂ : N₁ → N₁ × N₂)) = A₁.carrier ∧ AA.carrier.map (LinearMap.funLeft R C (AddMonoidHom.inr N₁ N₂ : N₂ → N₁ × N₂)) = A₂.carrier ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (z.1, 0)) ∈ AA.carrier) ∧ (∀ g ∈ AA.carrier, (fun z : N₁ × N₂ => g (0, z.2)) ∈ AA.carrier) ∧ ∀ c₁ c₂, HasColen R v A₁.carrier c₁ → HasColen R v A₂.carrier c₂ → HasColen R v AA.carrier (c₁ ^ Fintype.card N₂ * c₂ ^ Fintype.card N₁) := by
  first | exact @PositivityTheory.HtPt.Re.tens_hopf | exact PositivityTheory.HtPt.Re.tens_hopf
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TensorProductTightHopfOrders
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.tensor_product_tight_hopf_orders : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N₁ : Type) [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁], ∀ (N₂ : Type) [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂], ∀ (A₁ : HopfOrder (C := C) R N₁) (A₂ : HopfOrder (C := C) R N₂), (∀ x : N₁, p • x = 0) → (∀ x : N₂, p • x = 0) → IsTight v p A₁.carrier → IsTight v p A₂.carrier → IsTight v p (tens A₁.carrier A₂.carrier) := by
  intro p _ C _ _ _ v R _ _ hv hp N₁ _ _ _ N₂ _ _ _ A₁ A₂ _ _ h1 h2
  unfold IsTight at h1 h2 ⊢
  obtain ⟨a1, c1, o1, hA1, hC1, hO1, e1, f1⟩ := h1
  obtain ⟨a2, c2, o2, hA2, hC2, hO2, e2, f2⟩ := h2
  obtain ⟨AA, hAA, hl, hr, s1, s2, hcol⟩ := PositivityTheory.HtPt.Re.tens_hopf p C v R hv hp N₁ N₂ A₁ A₂
  rw [← hAA]
  have st1 : ∀ g ∈ AA.carrier, (fun x : N₁ × N₂ =>
      g ((AddMonoidHom.inl N₁ N₂) ((AddMonoidHom.fst N₁ N₂) x))) ∈ AA.carrier := by
    intro g hg
    simpa using s1 g hg
  have st2 : ∀ g ∈ AA.carrier, (fun x : N₁ × N₂ =>
      g ((AddMonoidHom.inr N₁ N₂) ((AddMonoidHom.snd N₁ N₂) x))) ∈ AA.carrier := by
    intro g hg
    simpa using s2 g hg
  have hAF := PositivityTheory.HtPt.Re.ret_af p C v R hv hp (N₁ × N₂) AA N₁ N₂ (AddMonoidHom.inl N₁ N₂)
    (AddMonoidHom.fst N₁ N₂) (AddMonoidHom.inr N₁ N₂) (AddMonoidHom.snd N₁ N₂)
    (fun y => by simp) (fun y => by simp) (fun x => by simp) (fun y => by simp) (fun y => by simp)
    st1 st2 a1 a2 (by rw [hl]; exact hA1) (by rw [hr]; exact hA2)
  have hOm := PositivityTheory.HtPt.Re.ret_om hv AA (AddMonoidHom.inl N₁ N₂)
    (AddMonoidHom.fst N₁ N₂) (AddMonoidHom.inr N₁ N₂) (AddMonoidHom.snd N₁ N₂)
    (fun y => by simp) (fun y => by simp) (fun x => by simp) (fun y => by simp) (fun y => by simp)
    st1 st2 o1 o2 (by rw [hl]; exact hO1) (by rw [hr]; exact hO2)
  refine ⟨a1 * a2, c1 ^ Fintype.card N₂ * c2 ^ Fintype.card N₁, o1 * o2, hAF, hcol c1 c2 hC1 hC2, hOm, ?_, ?_⟩
  · rw [Fintype.card_prod, mul_pow]
    have k1 : a1 ^ (Fintype.card N₁ * Fintype.card N₂ * (p - 1)) =
        (a1 ^ (Fintype.card N₁ * (p - 1))) ^ Fintype.card N₂ := by
      rw [← pow_mul]
      congr 1
      ring
    have k2 : a2 ^ (Fintype.card N₁ * Fintype.card N₂ * (p - 1)) =
        (a2 ^ (Fintype.card N₂ * (p - 1))) ^ Fintype.card N₁ := by
      rw [← pow_mul]
      congr 1
      ring
    rw [k1, k2, e1, e2]
    ring
  · rw [Fintype.card_prod, mul_pow]
    have k1 : o1 ^ (Fintype.card N₁ * Fintype.card N₂) = (o1 ^ Fintype.card N₁) ^ Fintype.card N₂ :=
      pow_mul _ _ _
    have k2 : o2 ^ (Fintype.card N₁ * Fintype.card N₂) = (o2 ^ Fintype.card N₂) ^ Fintype.card N₁ := by
      rw [← pow_mul, _root_.mul_comm (Fintype.card N₂)]
    rw [k1, k2, f1, f2]
    ring
end

