module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CongSpanSingleIff
section
noncomputable section

namespace MassDataIdxFrA

variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]

def IntVec (v : ι → F) : Prop := ∀ i, v i ∈ O

def CongSpan (S : Set (ι → F)) (v : ι → F) : Prop :=
  ∃ w ∈ Submodule.span O S, ∃ z : ι → F, IntVec O z ∧ v = w + (γ : F) • z



section Mat

open Matrix

variable {F : Type} [Field F] (O : ValuationSubring F) (γ : O) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem congSpan_zero (S : Set (ι → F)) : CongSpan O γ S 0 := by
  exact ⟨0, zero_mem _, 0, fun _ => zero_mem _, by simp⟩

theorem congSpan_neg (S : Set (ι → F)) (v : ι → F) : CongSpan O γ S (-v) ↔ CongSpan O γ S v := by
  have key : ∀ x, CongSpan O γ S x → CongSpan O γ S (-x) := by
    rintro x ⟨w, hw, z, hz, rfl⟩
    exact ⟨-w, neg_mem hw, -z, fun i => neg_mem (hz i), by rw [smul_neg, neg_add]⟩
  exact ⟨fun h => by simpa using key _ h, key v⟩

end Mat

end MassDataIdxFrA
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ExistsGl
section
noncomputable section

namespace MassDataIdxLatFree

open scoped Matrix
open Module

variable {K : Type} [Field K] (O : ValuationSubring K) [IsPrincipalIdealRing O]
  {n : Type} [Fintype n] [DecidableEq n]

theorem exists_gl (M : Submodule O (n → K)) (hfg : M.FG)
    (hsp : Submodule.span K (M : Set (n → K)) = ⊤) :
    ∃ P : GL n K, ∀ y, y ∈ M ↔ ∀ i, (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) i ∈ O := by
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex O M
  let bM : Module.Basis ι O M := Module.Free.chooseBasis O M
  let v : ι → (n → K) := fun i => (bM i : n → K)
  have hliO : LinearIndependent O v := bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing O K).mp hliO
  have hsmul : ∀ (r : O) (w : n → K), r • w = (r : K) • w := fun r w => rfl
  have hMsp : (M : Set (n → K)) ⊆ Submodule.span K (Set.range v) := by
    intro y hy
    have h1 := bM.sum_repr ⟨y, hy⟩
    have h2 : y = ∑ i, (bM.repr ⟨y, hy⟩ i : K) • v i := by
      have h3 := congrArg (fun m : M => (m : n → K)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
      conv_lhs => rw [← h3]
      rfl
    rw [h2]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hsp]
    exact Submodule.span_le.mpr hMsp
  let bK : Module.Basis ι K (n → K) := Module.Basis.mk hli hsp
  have hbK : ∀ i, bK i = v i := fun i => Module.Basis.mk_apply hli hsp i
  have hcard : Fintype.card ι = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fintype_fun_eq_card]
  let e : ι ≃ n := Fintype.equivOfCardEq hcard
  let Pm : Matrix n n K := fun i j => bK (e.symm j) i
  let Qm : Matrix n n K := fun i j => bK.repr (Pi.single j 1) (e.symm i)
  have hQ : ∀ y : n → K, Qm *ᵥ y = fun i => bK.repr y (e.symm i) := by
    intro y
    funext i
    have hy : y = ∑ j, y j • (Pi.single j (1 : K) : n → K) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hy]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, Qm]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hQP : Qm * Pm = 1 := by
    ext i k
    have h1 := congrFun (hQ (fun j => Pm j k)) i
    rw [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct] at h1
    rw [h1]
    have h2 : (fun j => Pm j k) = bK (e.symm k) := rfl
    rw [h2, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    simp [e.symm.injective.eq_iff, eq_comm]
  have hPQ : Pm * Qm = 1 := mul_eq_one_comm.mp hQP
  refine ⟨(⟨Pm, Qm, hPQ, hQP⟩ : GL n K), fun y => ?_⟩
  show y ∈ M ↔ ∀ i, (Qm *ᵥ y) i ∈ O
  rw [hQ]
  constructor
  · intro hy i
    have h2 : y = ∑ j, (bM.repr ⟨y, hy⟩ j : K) • bK j := by
      have h1 := bM.sum_repr ⟨y, hy⟩
      have h3 := congrArg (fun m : M => (m : n → K)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
      conv_lhs => rw [← h3]
      exact Finset.sum_congr rfl (fun j _ => by rw [hbK]; rfl)
    have h4 : bK.repr y (e.symm i) = (bM.repr ⟨y, hy⟩ (e.symm i) : K) := by
      conv_lhs => rw [h2]
      simp [Module.Basis.repr_self, Finsupp.single_apply]
    show bK.repr y (e.symm i) ∈ O
    rw [h4]
    exact (bM.repr ⟨y, hy⟩ (e.symm i)).2
  · intro hc
    have hc' : ∀ j, bK.repr y j ∈ O := by
      intro j
      have := hc (e j)
      simpa using this
    rw [← bK.sum_repr y]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have h5 : bK.repr y j • bK j = (⟨bK.repr y j, hc' j⟩ : O) • (bM j : n → K) := by
      rw [hsmul, hbK]
    rw [h5]
    exact M.smul_mem _ (bM j).2

end MassDataIdxLatFree
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ExistsGlOfLeftInv
section
namespace MassDataIdxAdA

open Matrix

variable {K : Type*} [Field K] (O : ValuationSubring K) {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_gl_of_left_inv (g : O) (hg : ¬ IsUnit g) (C R N : Matrix ι ι K)
    (hC : ∀ i j, C i j ∈ O) (hR : ∀ i j, R i j ∈ O) (hN : ∀ i j, N i j ∈ O)
    (hRC : R * C = 1 + (g : K) • N) :
    ∃ c : GL ι O, (c : Matrix ι ι O).map (fun x : O => (x : K)) = C := by
  classical
  set C' : Matrix ι ι O := Matrix.of fun i j => (⟨C i j, hC i j⟩ : O) with hC'
  set R' : Matrix ι ι O := Matrix.of fun i j => (⟨R i j, hR i j⟩ : O) with hR'
  set N' : Matrix ι ι O := Matrix.of fun i j => (⟨N i j, hN i j⟩ : O) with hN'
  have key : R' * C' = 1 + g • N' := by
    apply Matrix.map_injective (f := fun x : O => (x : K)) Subtype.val_injective
    ext i j
    have h := congrFun (congrFun hRC i) j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul] at h ⊢
    have hs : ((∑ k, R' i k * C' k j : O) : K) = ∑ k, R i k * C k j := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [show ((∑ k, R' i k * C' k j : O) : K) = algebraMap O K (∑ k, R' i k * C' k j) from rfl,
        map_sum]
      simp only [map_mul]
      rfl
    rw [hs, h]
    change _ = algebraMap O K ((1 : Matrix ι ι O) i j + g * N' i j)
    rw [map_add (f := _), map_mul]
    have hN'' : algebraMap O K (N' i j) = N i j := rfl
    have hg' : algebraMap O K g = (g : K) := rfl
    rw [hN'', hg']
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hres : IsLocalRing.residue O g = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hg
  have hone : IsUnit (1 + g • N').det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have : (IsLocalRing.residue O).mapMatrix (1 + g • N') = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [hres]
      · simp [hij, hres]
    rw [this, Matrix.det_one]
    exact one_ne_zero
  have hdet : IsUnit C'.det := by
    rw [← key, Matrix.det_mul] at hone
    exact (IsUnit.mul_iff.mp hone).2
  refine ⟨Matrix.nonsingInvUnit C' hdet, ?_⟩
  ext i j
  rfl

end MassDataIdxAdA
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FstMemSpan
section
noncomputable section

namespace MassDataIdxSpl

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}

def pr1 : (n → T) →ₗ[K] (n → K) where
  toFun v i := (θ (v i)).1
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

def pr2 : (n → T) →ₗ[K] (n → K) where
  toFun v i := (θ (v i)).2
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

theorem fst_apply_alt (v : n → T) (i : n) : pr1 θ v i = (θ (v i)).1 := rfl
theorem snd_apply_alt (v : n → T) (i : n) : pr2 θ v i = (θ (v i)).2 := rfl

variable {ι : Type} (Y : ι → n → T) (s : Set ι)

end MassDataIdxSpl
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff
section
noncomputable section

namespace MassDataIdxRed

open Matrix

theorem isUnit_of_map {R S : Type} [CommRing R] [IsLocalRing R] [Field S] (π : R →+* S)
    (hπ : Function.Surjective π) (r : R) (h : IsUnit (π r)) : IsUnit r := by
  by_contra hr
  have hk : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπ)
  have hm : r ∈ RingHom.ker π := by
    rw [hk]; exact (IsLocalRing.mem_maximalIdeal r).2 hr
  rw [RingHom.mem_ker] at hm
  rw [hm] at h
  exact not_isUnit_zero h

def glRed {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S) :
    GL ι R →* GL ι S :=
  Units.map (π.mapMatrix : Matrix ι ι R →+* Matrix ι ι S).toMonoidHom

theorem glRed_coe {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S)
    (A : GL ι R) : ((glRed π A : GL ι S) : Matrix ι ι S) = (A : Matrix ι ι R).map π := rfl

theorem glRed_surjective {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hloc : ∀ r, IsUnit (π r) → IsUnit r) :
    Function.Surjective (glRed (ι := ι) π) := by
  intro B
  choose f hf using hπ
  set A0 : Matrix ι ι R := (B : Matrix ι ι S).map f with hA0def
  have hA0 : A0.map π = (B : Matrix ι ι S) := by
    ext i j; simp [A0, hf]
  have hdet : IsUnit A0.det := by
    apply hloc
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA0]
    exact (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  refine ⟨Matrix.nonsingInvUnit A0 hdet, ?_⟩
  apply Units.ext
  rw [glRed_coe]
  exact hA0

theorem glRed_eq_one_iff {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (A : GL ι R) :
    glRed π A = 1 ↔ ∀ i j, ((A : Matrix ι ι R) - 1) i j ∈ RingHom.ker π := by
  rw [← Units.val_inj, glRed_coe, Units.val_one]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    rw [Matrix.map_apply] at hij
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro h
    ext i j
    have hij := h i j
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero] at hij
    rw [Matrix.map_apply, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end MassDataIdxRed
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.QuadRoot
section
noncomputable section

namespace MassDataIdxEmb

open Metric

theorem quad_root {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c0 c1 : K) (h1 : ‖c1‖ = 1) (h0 : ‖c0‖ < 1) :
    ∃ x : K, x * x + c1 * x + c0 = 0 := by
  have hnorm : ∀ x : K, ‖x‖ ≤ ‖c0‖ → ‖c1 + x‖ = 1 := by
    intro x hx
    have hne : ‖c1‖ ≠ ‖x‖ := by rw [h1]; exact (lt_of_le_of_lt hx h0).ne'
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, h1]
    exact max_eq_left (hx.trans h0.le)
  have hne0 : ∀ x : K, ‖x‖ ≤ ‖c0‖ → c1 + x ≠ 0 := fun x hx h => by
    have h' := hnorm x hx
    rw [h, norm_zero] at h'
    exact zero_ne_one h'
  set f : K → K := fun x => -c0 / (c1 + x) with hf
  have hmaps : Set.MapsTo f (closedBall 0 ‖c0‖) (closedBall 0 ‖c0‖) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    simp only [hf, norm_div, norm_neg, hnorm x hx, div_one, le_refl]
  haveI : IsClosed (closedBall (0 : K) ‖c0‖) := isClosed_closedBall
  haveI : CompleteSpace (closedBall (0 : K) ‖c0‖) := IsClosed.completeSpace_coe
  haveI : Nonempty (closedBall (0 : K) ‖c0‖) := ⟨⟨0, mem_closedBall_self (norm_nonneg _)⟩⟩
  have hcon : ContractingWith ⟨‖c0‖, norm_nonneg _⟩ (hmaps.restrict f _ _) := by
    refine ⟨NNReal.coe_lt_coe.1 (by rw [NNReal.coe_one]; exact h0),
      LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    have ha := mem_closedBall_zero_iff.1 a.2
    have hb := mem_closedBall_zero_iff.1 b.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    show ‖f a - f b‖ ≤ ‖c0‖ * ‖(a : K) - b‖
    have he : f a - f b = c0 * ((a : K) - b) / ((c1 + a) * (c1 + b)) := by
      simp only [hf]
      field_simp [hne0 _ ha, hne0 _ hb]
      ring
    rw [he, norm_div, norm_mul, norm_mul, hnorm _ ha, hnorm _ hb, mul_one, div_one]
  obtain ⟨x0, hx0e⟩ : ∃ x0 : closedBall (0 : K) ‖c0‖, hmaps.restrict f _ _ x0 = x0 :=
    ⟨_, hcon.fixedPoint_isFixedPt⟩
  have hfix : f (x0 : K) = x0 := congrArg Subtype.val hx0e
  refine ⟨(x0 : K), ?_⟩
  have hx0 := hne0 _ (mem_closedBall_zero_iff.1 x0.2)
  simp only [hf] at hfix
  rw [div_eq_iff hx0] at hfix
  linear_combination -hfix

end MassDataIdxEmb
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReindexGl
section
noncomputable section

namespace MassDataIdxCore

open Matrix

theorem reindex_gl {H R : Type} [Group H] [CommRing R] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (e : n ≃ ι) (I : Ideal R) (Q : H → Prop) (ψ : H →* GL n R) (hψ : Function.Surjective ψ)
    (hQ : ∀ h, (∀ i j, (((ψ h : GL n R) : Matrix n n R) - 1) i j ∈ I) ↔ Q h) :
    ∃ ψ' : H →* GL ι R, Function.Surjective ψ' ∧
      ∀ h, (∀ i j, (((ψ' h : GL ι R) : Matrix ι ι R) - 1) i j ∈ I) ↔ Q h := by
  classical
  let φ : GL n R ≃* GL ι R := Units.mapEquiv (Matrix.reindexAlgEquiv R R e).toMulEquiv
  refine ⟨φ.toMonoidHom.comp ψ, φ.surjective.comp hψ, fun h => ?_⟩
  rw [← hQ h]
  have key : ∀ i j, (((φ.toMonoidHom.comp ψ h : GL ι R) : Matrix ι ι R) - 1) i j =
      (((ψ h : GL n R) : Matrix n n R) - 1) (e.symm i) (e.symm j) := by
    intro i j
    simp [φ, Matrix.sub_apply, Matrix.one_apply, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  simp only [key]
  constructor
  · intro H i j
    simpa using H (e i) (e j)
  · intro H i j
    exact H _ _

end MassDataIdxCore
end
end

