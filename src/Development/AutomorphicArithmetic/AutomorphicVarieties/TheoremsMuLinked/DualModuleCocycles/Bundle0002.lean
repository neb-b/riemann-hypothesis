module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LcMat
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem lc_mat {Γ K : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) K)
    (h : ∀ a b, IsLocallyConstant fun g => f g a b) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : ∀ a b, ∀ᶠ y in nhds x, f y a b = f x a b := fun a b =>
    (IsLocallyConstant.iff_eventually_eq _).mp (h a b) x
  filter_upwards [Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr (hx a)] with y hy
  ext a b
  exact hy a b

theorem UpperTheory.V.Th.Coc.lc :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c c₀ : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X), (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → IsLift x δ (repR x ρ) τ c d → (IsLocallyConstant fun g => bar X (ρ g)) → (IsLocallyConstant fun g => δ (τ (MonoidAlgebra.single g 1))) → IsLocallyConstant fun g => c₀ • d (MonoidAlgebra.single g 1) := by
  intro O R X _ _ _ _ _ n G _ _ _ x δ ρ τ c c₀ d hspan hL hρ hτ
  have hsingle : ∀ g : G, repR x ρ (MonoidAlgebra.single g 1) = ρ g := by
    intro g
    rw [repR_single, map_one, one_smul]
  have hmulD : ∀ g h : G, d (MonoidAlgebra.single (g * h) 1) =
      d (MonoidAlgebra.single g 1) * bar X (ρ h) + bar X (ρ g) * d (MonoidAlgebra.single h 1) := by
    intro g h
    have e := hL.mul (MonoidAlgebra.single g 1) (MonoidAlgebra.single h 1)
    rw [MonoidAlgebra.single_mul_single, mul_one, hsingle, hsingle] at e
    exact e
  have hgen : ∀ h : G, IsLocallyConstant fun g => (d (MonoidAlgebra.single g 1) * bar X (ρ h)).trace := by
    intro h
    have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (ρ h)).trace) =
        fun g => c • δ (τ (MonoidAlgebra.single (g * h) 1)) -
          (bar X (ρ g) * d (MonoidAlgebra.single h 1)).trace := by
      funext g
      rw [← hL.tr, hmulD, Matrix.trace_add, add_sub_cancel_right]
    rw [e]
    refine IsLocallyConstant.sub ?_ ?_
    · exact (hτ.comp_continuous (continuous_mul_const h)).comp (fun y => c • y)
    · exact hρ.comp fun M => (M * d (MonoidAlgebra.single h 1)).trace
  have hspanLC : ∀ Z ∈ Submodule.span O (Set.range ρ),
      IsLocallyConstant fun g => (d (MonoidAlgebra.single g 1) * bar X Z).trace := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨h, rfl⟩ := hZ
      exact hgen h
    | zero =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (0 : Matrix (Fin n) (Fin n) O)).trace) =
          fun _ => 0 := by
        funext g
        have hb : bar X (0 : Matrix (Fin n) (Fin n) O) = 0 := by
          ext i j
          simp [bar]
        rw [hb, Matrix.mul_zero, Matrix.trace_zero]
      rw [e]
      exact IsLocallyConstant.const 0
    | add Z W _ _ hZ hW =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (Z + W)).trace) =
          fun g => (d (MonoidAlgebra.single g 1) * bar X Z).trace +
            (d (MonoidAlgebra.single g 1) * bar X W).trace := by
        funext g
        have hb : bar X (Z + W) = bar X Z + bar X W := by
          ext i j
          simp [bar]
        rw [hb, Matrix.mul_add, Matrix.trace_add]
      rw [e]
      exact hZ.add hW
    | smul k Z _ hZ =>
      have e : (fun g => (d (MonoidAlgebra.single g 1) * bar X (k • Z)).trace) =
          fun g => algebraMap O X k * (d (MonoidAlgebra.single g 1) * bar X Z).trace := by
        funext g
        have hb : bar X (k • Z) = algebraMap O X k • bar X Z := by
          ext i j
          simp [bar, Matrix.smul_apply, smul_eq_mul]
        rw [hb, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      rw [e]
      exact hZ.comp fun y => algebraMap O X k * y
  apply lc_mat
  intro a b
  have key : ∀ M : Matrix (Fin n) (Fin n) X,
      (M * bar X (c₀ • Matrix.of fun i j => if i = b ∧ j = a then (1:O) else 0)).trace = (c₀ • M) a b := by
    intro M
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, bar, Matrix.map_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_ite, smul_zero, smul_eq_mul, mul_one, ite_and]
    simp only [apply_ite (algebraMap O X), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Algebra.smul_def, mul_one]
    rw [mul_comm]
  have e : (fun g => (c₀ • d (MonoidAlgebra.single g 1)) a b) =
      fun g => (d (MonoidAlgebra.single g 1) *
        bar X (c₀ • Matrix.of fun i j => if i = b ∧ j = a then (1:O) else 0)).trace := by
    funext g
    rw [key]
  rw [e]
  exact hspanLC _ (hspan _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftOfS
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.liftOfS :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : E →+* Matrix (Fin n) (Fin n) O) (τ : E → R) (s : E →ₗ[R] Matrix (Fin n) (Fin n) R) (β : R) (b : O), IsDer x δ → (∀ (r : R) a, ρ (r • a) = x r • ρ a) → (∀ a, (ρ a).trace = x (τ a)) → x β = b → (∀ a a', s a * s a' = β • s (a * a')) → (∀ a, (s a).map x = b • ρ a) → (∀ a, (s a).trace = β * τ a) → ∃ d : E →+ Matrix (Fin n) (Fin n) X, IsLift x δ ρ τ (b * b) d := by
  intro O R X _ _ _ _ _ n E _ _ x δ ρ τ s β b hδ hρ htr hβ hs hx hst
  have hx' : ∀ a i j, x (s a i j) = b * ρ a i j := fun a i j => congrFun (congrFun (hx a) i) j
  have sm : ∀ (a : O) (y : X), a • y = algebraMap O X a * y := fun a y => Algebra.smul_def a y
  have en : ∀ a i j, (b • ((s a).map δ - δ β • bar X (ρ a))) i j =
      algebraMap O X b * (δ (s a i j) - δ β * algebraMap O X (ρ a i j)) := fun a i j => by
    rw [Matrix.smul_apply, sm]; rfl
  refine ⟨{ toFun := fun a => b • ((s a).map δ - δ β • bar X (ρ a))
            map_zero' := by ext i j; simp [bar]
            map_add' := fun a a' => by
              ext i j
              rw [Matrix.add_apply, en, en, en, map_add s, map_add ρ, Matrix.add_apply, Matrix.add_apply, map_add (f := _), map_add (f := _)]
              ring }, fun a a' => ?_, fun r a => ?_, fun a => ?_⟩
  · ext i k
    have h1 := congrArg δ (congrFun (congrFun (hs a a') i) k)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum, Matrix.smul_apply, smul_eq_mul, hδ β, hβ, hx'] at h1
    simp only [hδ _ _, hx', sm, map_mul] at h1
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_apply, Matrix.mul_apply, en, Matrix.map_apply]
    rw [mul_sub, eq_sub_of_add_eq h1.symm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · ext i j
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.add_apply, en]
    rw [Matrix.smul_apply, en, Matrix.smul_apply, map_smul s, hρ, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hδ r, hx']
    simp only [sm, map_mul, Matrix.map_apply]
    ring
  · have h1 : ((s a).map δ).trace = δ (s a).trace := by simp [Matrix.trace, map_sum]
    have h2 : (bar X (ρ a)).trace = algebraMap O X (ρ a).trace := by simp [bar, Matrix.trace, map_sum]
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.trace_smul, Matrix.trace_sub, h1, h2, hst, hδ _ _, hβ, htr]
    simp only [sm, map_mul, smul_eq_mul]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.StarFacts
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]

end

theorem UpperTheory.V.Th.Coc.starFacts :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R : Type} [CommRing O] [Algebra ℤ_[l] O] [CommRing R] [Algebra O R] {n : ℕ}, (∀ a b, F.star O R n (a * b) = F.star O R n b * F.star O R n a) ∧ (∀ a b, F.star O R n (a + b) = F.star O R n a + F.star O R n b) ∧ (∀ (r : R) a, F.star O R n (r • a) = r • F.star O R n a) ∧ (∀ a, F.star O R n (F.star O R n a) = a) ∧ (∀ g, F.star O R n (MonoidAlgebra.single g 1) = MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap O R ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O))) ∧ ∀ (x : R →ₐ[O] O) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O), F.IsForm O n ρ P → ∀ a, repR x (mat ρ) (F.star O R n a) = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (repR x (mat ρ) a)ᵀ * (P : Matrix (Fin n) (Fin n) O) := by
  intro l _ F O R _ _ _ _ n
  have hmul : ∀ a b, F.star O R n (a * b) = F.star O R n b * F.star O R n a := by
    intro a b
    simp [GFrame.star, map_mul]
  have hadd : ∀ a b, F.star O R n (a + b) = F.star O R n a + F.star O R n b := by
    intro a b
    simp [GFrame.star, map_add (f := _)]
  have hsmul : ∀ (r : R) a, F.star O R n (r • a) = r • F.star O R n a := by
    intro r a
    simp [GFrame.star, map_smul]
  have hzero : F.star O R n 0 = 0 := by
    simp [GFrame.star]
  have hsingle : ∀ g (r : R), F.star O R n (MonoidAlgebra.single g r)
      = MonoidAlgebra.single (F.conj g)⁻¹ (r * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
    intro g r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hepsR : ∀ g (k : ℤ), ((F.eps O R g ^ k : Rˣ) : R)
      = algebraMap O R ((F.eps O O g ^ k : Oˣ) : O) := by
    intro g k
    have h : F.eps O R g = Units.map (algebraMap O R).toMonoidHom (F.eps O O g) := by
      ext
      simp [GFrame.eps, pushCh]
    rw [h, ← map_zpow]
    rfl
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  have hcc : ∀ g, F.conj (F.conj g) = g := by
    intro g
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = g
    rw [hci, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]
  have hepsc : ∀ g, F.eps O R (F.conj g) = F.eps O R g := by
    intro g
    have h : F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
      show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = _
      rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_assoc, mul_inv_cancel, mul_one]
    simp [GFrame.eps, pushCh, h]
  refine ⟨hmul, hadd, hsmul, ?_, ?_, ?_⟩
  · intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => rw [hzero, hzero]
    | add f g hf hg => rw [hadd, hadd, hf, hg]
    | single g r =>
      rw [hsingle, hsingle]
      simp only [map_inv, hcc, inv_inv, hepsc]
      congr 1
      rw [mul_assoc, ← Units.val_mul, _root_.inv_zpow', ← _root_.zpow_add, add_neg_cancel, _root_.zpow_zero,
        Units.val_one, mul_one]
  · intro g
    rw [hsingle, one_mul, hepsR]
  · intro x ρ P hP a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp [hzero]
    | add f g hf hg =>
      rw [hadd, map_add (f := _), hf, hg, map_add (f := _), transpose_add, Matrix.mul_add, Matrix.add_mul]
    | single g r =>
      have key : ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
          = ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O) • mat ρ (F.conj g)⁻¹ := by
        have h := hP g
        have hm : mat ρ (F.conj g) * mat ρ (F.conj g)⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel, map_one]
        calc ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
            = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
              * (mat ρ (F.conj g) * mat ρ (F.conj g)⁻¹) := by rw [hm, mul_one]
          _ = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)
              * ((mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O) * mat ρ (F.conj g)) * mat ρ (F.conj g)⁻¹ := by
            simp only [mul_assoc]
          _ = _ := by
            rw [h, Matrix.mul_smul, Units.inv_mul, Matrix.smul_mul, one_mul]
      rw [hsingle, repR_single, repR_single, map_mul, hepsR, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        transpose_smul, Matrix.mul_smul, Matrix.smul_mul, key, mul_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TrRep
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.trRep :
    ∀ {O R G : Type} [CommRing O] [CommRing R] [Algebra O R] [Group G] {n : ℕ} (D : GDet n R G) (x : R →ₐ[O] O) (ρ : G →* Matrix (Fin n) (Fin n) O), 1 ≤ n → D.map x.toRingHom = GDet.ofRep ρ → (∀ y, (repR x ρ y).trace = x (D.tr y)) ∧ (∀ (r : R) y, repR x ρ (r • y) = x r • repR x ρ y) ∧ ∃ t : MonoidAlgebra R G →ₗ[R] R, ∀ y, t y = D.tr y := by
  intro O R G _ _ _ _ n D x ρ hn h
  refine ⟨fun y => ?_, fun r y => ?_, ?_⟩
  · have h1 := (((CA.d_gmap D).2.2.1 x.toRingHom y).2 1)
    rw [h] at h1
    have h2 := (CA.d_toDet (GDet.ofRep ρ) (MonoidAlgebra.mapRingHom G x.toRingHom y)).2.2.1
    rw [CA.d_toDet_ofRep.1 ρ, (CA.d_ofRep _ _ _).2.2.1 hn] at h2
    exact h2.trans h1
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]
    | single g a =>
      rw [MonoidAlgebra.smul_single, repR_single, repR_single, smul_eq_mul, map_mul, mul_smul]
  · obtain ⟨t, ht⟩ := (CA.d_tr D.toDet).1 hn
    exact ⟨t, fun y => (ht y).trans (CA.d_toDet D y).2.2.1⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TrSingle
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem corner_eq {R : Type} [CommRing R] {n : ℕ} {E : Type} [Ring E] [Algebra R E] {τ : E →ₗ[R] R}
    {e : Fin n → E} (h : IsTrGMA τ e) (i : Fin n) (z : E) (hz : e i * z * e i = z) : z = τ z • e i := by
  have hidem : e i * e i = e i := (h.idem.idem i).eq
  have h1 : e i * z = z := by
    calc e i * z = e i * (e i * z * e i) := by rw [hz]
      _ = e i * z * e i := by rw [← mul_assoc, ← mul_assoc, hidem]
      _ = z := hz
  calc z = e i * z * e i := hz.symm
    _ = τ (e i * z) • e i := h.corner i z
    _ = τ z • e i := by rw [h1]

private theorem tr_single {O : Type} [CommRing O] {n : ℕ} (o i j : Fin n) (c : O) (A : Matrix (Fin n) (Fin n) O) :
    ((c • Matrix.single o i (1 : O)) * A * (c • Matrix.single j o (1 : O))).trace = c ^ 2 * A i j := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.single_mul_mul_single]
  simp [Matrix.trace_smul, pow_two, mul_assoc]

theorem UpperTheory.V.Th.Coc.smat :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (ρ : E →+* Matrix (Fin n) (Fin n) O) (τ : E →ₗ[R] R) (e : Fin n → E) (c : O), 1 ≤ n → IsTrGMA τ e → (∀ i, ρ (e i) = Matrix.single i i 1) → (∀ a, (ρ a).trace = x (τ a)) → (∀ Z, ∃ a, ρ a = c • Z) → ∃ (s : E →ₗ[R] Matrix (Fin n) (Fin n) R) (β : R), x β = c ^ (2 * n) ∧ (∀ a b, s a * s b = β • s (a * b)) ∧ (∀ a, (s a).map x = c ^ (2 * n) • ρ a) ∧ ∀ a, (s a).trace = β * τ a := by
  intro O R _ _ _ n E _ _ x ρ τ e c hn hT hρe htr hsurj
  classical
  obtain ⟨o, -⟩ : ∃ o : Fin n, True := ⟨⟨0, hn⟩, trivial⟩
  have hidem : ∀ i, e i * e i = e i := fun i => (hT.idem.idem i).eq
  have hρE : ∀ (i j : Fin n) (r : O), Matrix.single i i (1 : O) * (r • Matrix.single i j (1 : O)) *
      Matrix.single j j (1 : O) = r • Matrix.single i j (1 : O) := by
    intro i j r
    ext u v
    simp only [Matrix.single_mul_mul_single, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all
  choose hh hhρ using fun i : Fin n => hsurj (Matrix.single o i (1 : O))
  choose kk kkρ using fun j : Fin n => hsurj (Matrix.single j o (1 : O))
  obtain ⟨p, hp⟩ : ∃ p : Fin n → E, ∀ i, p i = e o * hh i * e i := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin n → E, ∀ j, q j = e j * kk j * e o := ⟨_, fun _ => rfl⟩
  have ρp : ∀ i, ρ (p i) = c • Matrix.single o i (1 : O) := by
    intro i
    simp only [hp, map_mul, hρe, hhρ]
    exact hρE o i c
  have ρq : ∀ j, ρ (q j) = c • Matrix.single j o (1 : O) := by
    intro j
    simp only [hq, map_mul, hρe, kkρ]
    exact hρE j o c
  have hpl : ∀ i, e o * p i = p i := by
    intro i
    simp only [hp, ← mul_assoc, hidem]
  have hpr : ∀ i, p i * e i = p i := by
    intro i
    simp only [hp, mul_assoc, hidem]
  have hql : ∀ j, e j * q j = q j := by
    intro j
    simp only [hq, ← mul_assoc, hidem]
  have hqr : ∀ j, q j * e o = q j := by
    intro j
    simp only [hq, mul_assoc, hidem]
  have hcorner : ∀ i z, e i * z * e i = z → z = τ z • e i := fun i z hz => corner_eq hT i z hz
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → R, ∀ j, γ j = τ (q j * p j) := ⟨_, fun _ => rfl⟩
  have hqp : ∀ j, q j * p j = γ j • e j := by
    intro j
    rw [hγ]
    apply hcorner
    rw [← mul_assoc, hql, mul_assoc, hpr]
  have hxγ : ∀ j, x (γ j) = c ^ 2 := by
    intro j
    rw [hγ, ← htr, map_mul, ρq, ρp]
    have h := tr_single j o o c (1 : Matrix (Fin n) (Fin n) O)
    rw [Matrix.mul_one, Matrix.one_apply_eq, mul_one] at h
    exact h
  have hρs : ∀ r : R, ρ (r • e o) = Matrix.single o o (x r) := by
    intro r
    have hz : e o * (r • e o) * e o = r • e o := by
      rw [mul_smul_comm, smul_mul_assoc, hidem, hidem]
    have h1 : ρ (r • e o) = Matrix.single o o ((ρ (r • e o)) o o) := by
      conv_lhs => rw [← hz]
      rw [map_mul, map_mul, hρe, Matrix.single_mul_mul_single, one_mul, mul_one]
    have h2 : (ρ (r • e o)).trace = x r := by
      rw [htr, map_smul, hT.one, smul_eq_mul, mul_one]
    rw [h1] at h2 ⊢
    congr 1
    simpa [Matrix.trace, Matrix.single_apply] using h2
  obtain ⟨Γj, hΓj⟩ : ∃ Γj : Fin n → R, ∀ j, Γj j = ∏ l ∈ Finset.univ.erase j, γ l := ⟨_, fun _ => rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q' : Fin n → E, ∀ j, q' j = q j * (Γj j • e o) := ⟨_, fun _ => rfl⟩
  have hq'p : ∀ j, q' j * p j = (∏ l, γ l) • e j := by
    intro j
    rw [hq', mul_smul_comm, smul_mul_assoc, hqr, hqp, smul_smul, hΓj,
      Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have hsum : ∑ j, q' j * p j = (∏ l, γ l) • (1 : E) := by
    simp_rw [hq'p]
    rw [← Finset.smul_sum, hT.idem.complete]
  have hq'r : ∀ j, q' j * e o = q' j := by
    intro j
    rw [hq', mul_assoc, smul_mul_assoc, hidem]
  have hX : ∀ i j a, p i * a * q' j = τ (p i * a * q' j) • e o := by
    intro i j a
    apply hcorner
    have h : e o * (p i * a * q' j) * e o = (e o * p i) * a * (q' j * e o) := by simp only [mul_assoc]
    rw [h, hpl, hq'r]
  have hτmul : ∀ i k j a b, τ (p i * a * q' k) * τ (p k * b * q' j) =
      τ (p i * a * q' k * (p k * b * q' j)) := by
    intro i k j a b
    have hl : e o * (p k * b * q' j) = p k * b * q' j := by simp only [← mul_assoc, hpl]
    conv_rhs => rw [hX i k a, smul_mul_assoc, hl, map_smul, smul_eq_mul]
  have hρq' : ∀ j, ρ (q' j) = x (Γj j) • (c • Matrix.single j o (1 : O)) := by
    intro j
    rw [hq', map_mul, ρq, hρs]
    ext u v
    simp only [Matrix.smul_mul, Matrix.single_mul_single_same, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> ring
  have hxΓj : ∀ j, x (Γj j) = (c ^ 2) ^ (n - 1) := by
    intro j
    rw [hΓj, map_prod]
    simp_rw [hxγ]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  let s : E →ₗ[R] Matrix (Fin n) (Fin n) R :=
    { toFun := fun a => Matrix.of fun i j => τ (p i * a * q' j)
      map_add' := by
        intro a b
        ext i j
        simp only [Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, map_add (f := _)]
      map_smul' := by
        intro r a
        ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul,
          RingHom.id_apply] }
  have hs : ∀ a i j, s a i j = τ (p i * a * q' j) := fun _ _ _ => rfl
  refine ⟨s, ∏ l, γ l, ?_, ?_, ?_, ?_⟩
  · rw [map_prod]
    simp_rw [hxγ]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  · intro a b
    ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply, hs, smul_eq_mul]
    simp_rw [hs, hτmul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    have hrw : ∑ k, p i * a * q' k * (p k * b * q' j) = p i * a * (∑ k, q' k * p k) * b * q' j := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by simp only [mul_assoc]
    rw [hrw, hsum, mul_smul_comm, mul_one, smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul,
      mul_assoc (p i) a b]
  · intro a
    ext i j
    rw [Matrix.map_apply, hs, Matrix.smul_apply, smul_eq_mul, ← htr, map_mul, map_mul, ρp, hρq',
      Matrix.mul_smul, Matrix.trace_smul, tr_single, smul_eq_mul, hxΓj, ← mul_assoc, ← pow_succ,
      ← pow_mul, Nat.sub_add_cancel hn]
  · intro a
    have hc : ∀ i, τ (p i * a * q' i) = τ (a * (q' i * p i)) := by
      intro i
      rw [mul_assoc, hT.comm, mul_assoc]
    simp only [Matrix.trace, Matrix.diag_apply, hs, hc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← Finset.mul_sum, hsum, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TriAeval
section
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem tri_pow {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O)
    (h : ∀ a b, b < a → u a b = 0) (hd : ∀ i, u i i = α i) (k : ℕ) :
    (∀ a b, b < a → (u ^ k) a b = 0) ∧ ∀ i, (u ^ k) i i = α i ^ k := by
  induction k with
  | zero =>
    refine ⟨fun a b hab => ?_, fun i => by simp⟩
    simp [Matrix.one_apply_ne hab.ne']
  | succ k ih =>
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      rcases lt_or_ge c a with hc | hc
      · rw [ih.1 a c hc, zero_mul]
      · rw [h c b (lt_of_lt_of_le hab hc), mul_zero]
    · rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [ih.2, hd, pow_succ]
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · rw [ih.1 i c hc, zero_mul]
        · rw [h c i hc, mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi

private theorem tri_aeval {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O)
    (h : ∀ a b, b < a → u a b = 0) (hd : ∀ i, u i i = α i) (p : Polynomial O) :
    (∀ a b, b < a → (Polynomial.aeval u p) a b = 0) ∧ ∀ i, (Polynomial.aeval u p) i i = p.eval (α i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [map_add (f := _), Matrix.add_apply, hp.1 a b hab, hq.1 a b hab, add_zero]
    · rw [map_add (f := _), Matrix.add_apply, hp.2, hq.2, Polynomial.eval_add]
  | monomial k c =>
    have hk := tri_pow u α h hd k
    rw [Polynomial.aeval_monomial, ← Algebra.smul_def]
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · rw [Matrix.smul_apply, hk.1 a b hab, smul_zero]
    · rw [Matrix.smul_apply, hk.2, Polynomial.eval_monomial, smul_eq_mul]

theorem UpperTheory.V.Th.Coc.flagB :
    ∀ {O : Type} [CommRing O] {n : ℕ} (u : Matrix (Fin n) (Fin n) O) (α : Fin n → O), (∀ a b, b < a → u a b = 0) → (∀ i, u i i = α i) → (∀ a b, b < a → kS u α a b = 0 ∧ kT u α a b = 0) ∧ ∀ i, kS u α i i = ∏ j ∈ Finset.univ.erase i, (α i - α j) ∧ kT u α i i = ∏ j ∈ Finset.univ.erase i, (α i - α j) := by
  intro O _ n u α h hd
  have hev : ∀ i k, (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (α j))).eval (α k) =
      ∏ j ∈ Finset.univ.erase i, (α k - α j) := by
    intro i k
    simp [Polynomial.eval_prod]
  refine ⟨fun a b hab => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · exact (tri_aeval u α h hd _).1 a b hab
  · exact (tri_aeval u α h hd _).1 a b hab
  · show kEl u α i i i = _
    rw [kEl, (tri_aeval u α h hd _).2 i, hev]
  · show kEl u α i i i = _
    rw [kEl, (tri_aeval u α h hd _).2 i, hev]
end

