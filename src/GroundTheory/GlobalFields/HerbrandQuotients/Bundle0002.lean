module

public import Mathlib
public import GroundTheory.TateCohomology.HerbrandAbstract
public import GroundTheory.GlobalFields.HerbrandQuotients.Bundle0001
public import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm

@[expose] public section

-- bundled from GroundTheory.GlobalFields.HerbrandQuotients.Lattice
section
namespace GroundTheory.Global

open GroundTheory.GroupCoh
open scoped TensorProduct

theorem finite_quotient_of_smul_mem {B : Type*} [AddCommGroup B] [Module.Finite ℤ B]
    (S : AddSubgroup B) {n : ℤ} (hn : n ≠ 0) (h : ∀ y, n • y ∈ S) : Finite (B ⧸ S) := by
  have : Module.Finite ℤ (B ⧸ S) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' S).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective S y
  refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
  show n • (QuotientAddGroup.mk' S x) = 0
  rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact h x

variable {G M M' : Type*} [Group G] [AddCommGroup M] [AddCommGroup M']

theorem cyclicHerbrand_eq_of_injective [Fintype G] (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (σ : G) (φ : M →+ M') (hφ : Function.Injective φ)
    [Finite (M' ⧸ φ.range)] (hcomm : ∀ g x, φ (ρ g x) = ρ' g (φ x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ :=
  herbrandQuotient_eq_of_injective_of_finite (fA := cycSub ρ σ) (gA := normHom ρ)
    (fB := cycSub ρ' σ) (gB := normHom ρ') hφ
    (fun a => by rw [cycSub_apply, cycSub_apply, map_sub, hcomm])
    (fun a => by rw [normHom_apply, normHom_apply, map_sum]; simp only [hcomm])
    (cycSub_normHom ρ' σ) (normHom_cycSub ρ' σ)

theorem exists_injective_intertwiner_of_basis {ι : Type*} [Fintype ι]
    (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x))
    (b : Module.Basis ι ℤ M) (b' : Module.Basis ι ℤ M') :
    ∃ φ : M →ₗ[ℤ] M', Function.Injective φ ∧ (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ g x, φ (ρ g x) = ρ' g (φ x) := by
  classical

  let bR := Algebra.TensorProduct.basis ℝ b
  let bR' := Algebra.TensorProduct.basis ℝ b'
  let A : G → Matrix ι ι ℤ := fun g => LinearMap.toMatrix b b (ρ g)
  let A' : G → Matrix ι ι ℤ := fun g => LinearMap.toMatrix b' b' (ρ' g)
  let P : Matrix ι ι ℝ := LinearMap.toMatrix bR bR' e.toLinearMap
  have hP : P.det ≠ 0 := by
    have hid : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
      LinearMap.ext fun x => by simp
    have h1 := congrArg (LinearMap.toMatrix bR bR) hid
    rw [LinearMap.toMatrix_comp bR bR' bR, LinearMap.toMatrix_id] at h1
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact right_ne_zero_of_mul_eq_one h2
  have hPA : ∀ g, P * (A g).map (Int.cast : ℤ → ℝ) = (A' g).map (Int.cast : ℤ → ℝ) * P := by
    intro g
    have hc : e.toLinearMap ∘ₗ (ρ g).baseChange ℝ = (ρ' g).baseChange ℝ ∘ₗ e.toLinearMap :=
      LinearMap.ext (he g)
    have h1 := congrArg (LinearMap.toMatrix bR bR') hc
    rw [LinearMap.toMatrix_comp bR bR bR', LinearMap.toMatrix_comp bR bR' bR',
      LinearMap.toMatrix_baseChange, LinearMap.toMatrix_baseChange, algebraMap_int_eq] at h1
    exact h1

  obtain ⟨Q, hQ, hQA⟩ := exists_rat_intertwiner (fun g => (A g).map (Int.cast : ℤ → ℚ))
    (fun g => (A' g).map (Int.cast : ℤ → ℚ)) P hP (fun g => by
      rw [Matrix.map_map, Matrix.map_map]
      convert hPA g using 3 <;> ext x <;> simp)

  obtain ⟨⟨d, hd⟩, hdQ⟩ := IsLocalization.exist_integer_multiples (R := ℤ)
    (M := nonZeroDivisors ℤ) (S := ℚ) Finset.univ (fun p : ι × ι => Q p.1 p.2)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose D hD using fun a b => RingHom.mem_rangeS.1 (hdQ (a, b) (Finset.mem_univ _))
  let Dm : Matrix ι ι ℤ := Matrix.of D
  have hDm : Dm.map (Int.cast : ℤ → ℚ) = (d : ℚ) • Q := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Dm, Matrix.of_apply]
    rw [← eq_intCast (algebraMap ℤ ℚ), hD a b, zsmul_eq_mul, smul_eq_mul]
  have hdet : Dm.det ≠ 0 := by
    have h1 : (Dm.det : ℚ) = (d : ℚ) ^ Fintype.card ι * Q.det := by
      rw [Int.cast_det]
      change (Dm.map (Int.cast : ℤ → ℚ)).det = _
      rw [hDm, Matrix.det_smul]
    intro h0
    rw [h0, Int.cast_zero] at h1
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hd0)) hQ h1.symm
  have hmap : ∀ X Y : Matrix ι ι ℤ, (X * Y).map (Int.cast : ℤ → ℚ) =
      X.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ) := fun X Y =>
    Matrix.map_mul (f := Int.castRingHom ℚ)
  have hDA : ∀ g, Dm * A g = A' g * Dm := by
    intro g
    apply Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective
    show (Dm * A g).map (Int.cast : ℤ → ℚ) = (A' g * Dm).map (Int.cast : ℤ → ℚ)
    rw [hmap, hmap, hDm, Matrix.smul_mul, Matrix.mul_smul, hQA g]

  let φ : M →ₗ[ℤ] M' := Matrix.toLin b b' Dm
  refine ⟨φ, ?_, ⟨Dm.det, hdet, fun y => ?_⟩, fun g x => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := Matrix.repr_toLin (v₁ := b) (v₂ := b') Dm x
    rw [show Matrix.toLin b b' Dm x = 0 from hx, map_zero] at h1
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1.symm
    exact b.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => congrFun h2 i)
  · refine ⟨Matrix.toLin b' b Dm.adjugate y, ?_⟩
    show (Matrix.toLin b b' Dm ∘ₗ Matrix.toLin b' b Dm.adjugate) y = _
    rw [← Matrix.toLin_mul, Matrix.mul_adjugate, map_smul, Matrix.toLin_one,
      LinearMap.smul_apply, LinearMap.id_apply]
  · have h1 : φ ∘ₗ ρ g = ρ' g ∘ₗ φ := by
      apply (LinearMap.toMatrix b b').injective
      rw [LinearMap.toMatrix_comp b b b', LinearMap.toMatrix_comp b b' b',
        LinearMap.toMatrix_toLin]
      exact hDA g
    exact LinearMap.congr_fun h1 x

variable [Module.Finite ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M'] [Module.Free ℤ M']

theorem exists_injective_intertwiner_of_real_equiv (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    ∃ φ : M →ₗ[ℤ] M', Function.Injective φ ∧ (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ g x, φ (ρ g x) = ρ' g (φ x) := by
  let b := Module.Free.chooseBasis ℤ M
  let b₀ := Module.Free.chooseBasis ℤ M'
  have h1 := e.finrank_eq
  rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b),
    Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b₀)] at h1
  exact exists_injective_intertwiner_of_basis ρ ρ' e he b
    (b₀.reindex (Fintype.equivOfCardEq h1).symm)

theorem cyclicHerbrand_eq_of_real_equiv [Fintype G] (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (σ : G) (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ := by
  obtain ⟨φ, hφ, ⟨n, hn, hrange⟩, hcomm⟩ := exists_injective_intertwiner_of_real_equiv ρ ρ' e he
  have : Finite (M' ⧸ φ.toAddMonoidHom.range) :=
    finite_quotient_of_smul_mem _ hn fun y => by
      obtain ⟨x, hx⟩ := hrange y
      exact ⟨x, hx⟩
  exact cyclicHerbrand_eq_of_injective ρ ρ' σ φ.toAddMonoidHom hφ hcomm

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.HerbrandQuotients.SUnitsExact
section
namespace GroundTheory.Global

open GroundTheory.GroupCoh

variable {G A B C : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C]

theorem hasHerbrandQuotient_cycSubOne_of_finite [Module.Finite ℤ A] (ρ : Representation ℤ G A)
    {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne ρ σ) (cycNorm ρ) :=
  hasCyclicHerbrand_of_finite ρ hσ

theorem cycHerbrand_eq_mul_of_exact (ρA : Representation ℤ G A) (ρB : Representation ℤ G B)
    (ρC : Representation ℤ G C) (σ : G) {i : A →+ B} {p : B →+ C} (hi : Function.Injective i)
    (hex : Function.Exact i p) [Finite (C ⧸ p.range)]
    (hiG : ∀ g a, i (ρA g a) = ρB g (i a)) (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hA : HasHerbrandQuotient (cycSubOne ρA σ) (cycNorm ρA))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρA σ * cycHerbrand ρC σ := by
  have hfS : ∀ x ∈ p.range, cycSubOne ρC σ x ∈ p.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨cycSubOne ρB σ b, by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]⟩
  have hgS : ∀ x ∈ p.range, cycNorm ρC x ∈ p.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨cycNorm ρB b, by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG]⟩
  have : p.range.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have hR := (hasHerbrandQuotient_restrictEnd_iff p.range hfS hgS (cycSubOne_cycNorm ρC σ)
    (cycNorm_cycSubOne ρC σ)).2 hC
  have hex' : Function.Exact i p.rangeRestrict := by
    intro b
    rw [← hex b]
    constructor
    · intro h
      simpa using congrArg Subtype.val h
    · intro h
      exact Subtype.ext (by simpa using h)
  rw [cycHerbrand, cycHerbrand, cycHerbrand, ← herbrandQuotient_restrictEnd p.range hfS hgS
    (cycSubOne_cycNorm ρC σ) (cycNorm_cycSubOne ρC σ)]
  exact herbrandQuotient_eq_mul_of_shortExact hi p.rangeRestrict_surjective hex'
    (fun a => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hiG])
    (fun a => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hiG])
    (fun b => Subtype.ext (by
      change p (cycSubOne ρB σ b) = cycSubOne ρC σ (p b)
      rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]))
    (fun b => Subtype.ext (by
      change p (cycNorm ρB b) = cycNorm ρC (p b)
      rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG]))
    (cycSubOne_cycNorm ρB σ) (cycNorm_cycSubOne ρB σ) hA hR

theorem cycHerbrand_eq_of_surjective_of_finite_ker (ρB : Representation ℤ G B)
    (ρC : Representation ℤ G C) (σ : G) {p : B →+ C} (hp : Function.Surjective p)
    [Finite p.ker] (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρC σ := by
  have hfK : ∀ x ∈ p.ker, cycSubOne ρB σ x ∈ p.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    rw [cycSubOne_apply, map_sub, hpG, hx, map_zero, sub_zero]
  have hgK : ∀ x ∈ p.ker, cycNorm ρB x ∈ p.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cycNorm_apply, map_sum]
    simp [hpG, hx]
  have hfgK : ∀ x, restrictEnd (cycSubOne ρB σ) p.ker hfK
      (restrictEnd (cycNorm ρB) p.ker hgK x) = 0 := fun x =>
    Subtype.ext (by
      change cycSubOne ρB σ (cycNorm ρB x.val) = 0
      exact cycSubOne_cycNorm ρB σ x.val)
  have hgfK : ∀ x, restrictEnd (cycNorm ρB) p.ker hgK
      (restrictEnd (cycSubOne ρB σ) p.ker hfK x) = 0 := fun x =>
    Subtype.ext (by
      change cycNorm ρB (cycSubOne ρB σ x.val) = 0
      exact cycNorm_cycSubOne ρB σ x.val)
  have hA : HasHerbrandQuotient (restrictEnd (cycSubOne ρB σ) p.ker hfK)
      (restrictEnd (cycNorm ρB) p.ker hgK) := hasHerbrandQuotient_of_finite _ _
  have hex : Function.Exact p.ker.subtype p := by
    intro b
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cycHerbrand, cycHerbrand,
    herbrandQuotient_eq_mul_of_shortExact p.ker.subtype_injective hp hex
      (fun _ => rfl) (fun _ => rfl)
      (fun b => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG])
      (fun b => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG])
      (cycSubOne_cycNorm ρB σ) (cycNorm_cycSubOne ρB σ) hA hC,
    herbrandQuotient_eq_one_of_finite hfgK hgfK, one_mul]

theorem cycHerbrand_prod (ρA : Representation ℤ G A) (ρB : Representation ℤ G B) (σ : G)
    (hA : HasHerbrandQuotient (cycSubOne ρA σ) (cycNorm ρA))
    (hB : HasHerbrandQuotient (cycSubOne ρB σ) (cycNorm ρB)) :
    cycHerbrand (ρA.prod ρB) σ = cycHerbrand ρA σ * cycHerbrand ρB σ := by
  have : Finite (B ⧸ (AddMonoidHom.snd A B).range) := by
    rw [AddMonoidHom.range_eq_top.2 (fun b => ⟨(0, b), rfl⟩)]
    infer_instance
  refine cycHerbrand_eq_mul_of_exact ρA (ρA.prod ρB) ρB σ (i := AddMonoidHom.inl A B)
    (p := AddMonoidHom.snd A B) (fun a a' h => congrArg Prod.fst h) ?_ (fun g a => ?_)
    (fun g b => rfl) hA hB
  · rintro ⟨a, b⟩
    simp only [AddMonoidHom.coe_snd, Set.mem_range, AddMonoidHom.inl_apply, Prod.ext_iff]
    constructor
    · rintro rfl
      exact ⟨a, rfl, rfl⟩
    · rintro ⟨a', -, rfl⟩
      rfl
  · exact Prod.ext rfl (map_zero (ρB g)).symm

end GroundTheory.Global
end

