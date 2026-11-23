module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipRat
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemFlag
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.Pf.FlagCoordinates

variable {D : D7} (X : HidaSetting D)

theorem gE_sub_one (Z : Matrix (Kap X) (Kap X) X.B.I.E) :
    Formalism.L2.SG.Pf.UnipB.gE X Z - 1 = Bm X * (cay (N0 D) Z - 1) * Bm' X := by
  unfold Formalism.L2.SG.Pf.UnipB.gE
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bm_mul_Bm']

theorem Bm_mulVec_mem (S : Set (Fin D.R.rS)) (c : Kap X → X.B.I.E) (hc : ∀ k, k ∉ Sum.inl '' S → c k = 0) :
    Bm X *ᵥ c ∈ Submodule.span X.B.I.E (X.eR '' S) := by
  rw [Bm_mulVec]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ Sum.inl '' S
  · obtain ⟨b, hb, rfl⟩ := hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [hc k hk, zero_smul]
    exact Submodule.zero_mem _

theorem flag_coord {Z : Matrix (Kap X) (Kap X) X.B.I.E} (hZ : InPat (lvk X) 1 Z) (a : Fin D.R.rS) :
    (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ X.eR a ∈ Submodule.span X.B.I.E (X.eR '' {b | b.1 < a.1}) := by
  rw [gE_sub_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hB : Bm' X *ᵥ X.eR a = Pi.single (Sum.inl a) 1 := by
    rw [Bm'_mulVec]
    funext k
    rw [show X.eR a = bv X (Sum.inl a) from rfl, cE_bv]
    simp [Pi.single_apply]
  rw [hB]
  refine Bm_mulVec_mem X _ _ fun k hk => ?_
  rw [mulVec_single_one]
  refine cay_sub_one _ hZ k _ ?_
  rcases k with b | i | b
  · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
    simp only [lvk, Sum.elim_inl]; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega

theorem orth_coord {Z : Matrix (Kap X) (Kap X) X.B.I.E} (hZ : InPat (lvk X) 1 Z) (x : Fin X.B.I.n → X.B.I.E)
    (hx : ∀ a, hE X (X.eR a) x = 0) :
    (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ x ∈ Submodule.span X.B.I.E (X.eR '' Set.univ) := by
  rw [gE_sub_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Bm'_mulVec]
  refine Bm_mulVec_mem X Set.univ _ fun k hk => ?_
  have hk' : ∀ b, k ≠ Sum.inl b := by
    rintro b rfl
    exact hk ⟨b, Set.mem_univ _, rfl⟩
  rw [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hlk := lvk_notinl X k hk'
  rcases j with b | i | b
  · rw [cay_sub_one _ hZ k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
  · rw [cay_sub_one _ hZ k _ (by rw [lvk_w]; omega), zero_mul]
  · rw [show cE X x (Sum.inr (Sum.inr b)) = hE X (X.eR b) x from rfl, hx b, mul_zero]

theorem crd_desc (S : Set (Fin D.R.rS)) (v : (VS D).V)
    (hv : X.crd v ∈ Submodule.span X.B.I.E (X.eR '' S)) :
    v ∈ Submodule.span D.host.E (X.eX '' S) := by
  obtain ⟨c, hc⟩ := (Fintype.mem_span_image_iff_exists_fun X.B.I.E).1 hv
  have e : v = ∑ i : S, X.ιE (c i) • X.eX i := by
    rw [← Formalism.L2.SG.Pf.Level.toV_crd X v, ← hc, Formalism.L2.SG.Pf.Level.toV_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Formalism.L2.SG.Pf.Level.toV_smul, show X.eR i = X.crd (X.eX i) from rfl, Formalism.L2.SG.Pf.Level.toV_crd]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, i.2, rfl⟩)

end Formalism.L2.SG.Pf.FlagCoordinates

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Pf.FlagCoordinates

theorem memFlagOf_holds : MemFlagOf := by
  intro D X u Z n hZ hn
  have hm : ∀ v, (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ X.crd v = X.crd (n v - v) := fun v => Formalism.L2.SG.Pf.Vanish2.mcrd X hn v
  have hXf : ∀ k, Xflag (lf D (X.Fu u)) k = Submodule.span D.host.E (X.eX '' {i | i.1 < k}) := by
    intro k
    show Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < k}) = _
    rw [X.Fu_e]
  have hXs : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (X.eX '' Set.univ) := by
    show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
    rw [X.Fu_e, Set.image_univ]
  have he : ∀ a : Fin D.R.rS, n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {b | b.1 < a.1}) := by
    intro a
    have hd := flag_coord X hZ a
    rw [show X.eR a = X.crd (X.eX a) from rfl, hm] at hd
    exact crd_desc X _ _ hd
  refine ⟨fun j x hx => ?_, fun x hx => ?_⟩
  · rw [hXf] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      refine Submodule.span_mono ?_ (he a)
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨b, lt_of_lt_of_le hb (Nat.lt_succ_iff.1 ha), rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _), add_sub_add_comm]
      exact add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ hy
  · have hx0 : ∀ a, hE X (X.eR a) (X.crd x) = 0 := by
      intro a
      have hmem : X.eX a ∈ Xsp (lf D (X.Fu u)) := by
        rw [hXs]
        exact Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩
      have h0 : (VS D).hT (X.eX a) x = 0 := (Formalism.L2.SG.Pf.mem_orth_iff _ _).1 hx _ hmem
      rw [show X.eR a = X.crd (X.eX a) from rfl, hE_crd, h0, map_zero]
    have hd := orth_coord X hZ _ hx0
    rw [hm] at hd
    rw [hXs]
    exact crd_desc X _ _ hd

end Formalism.L2.SG.TermOp.Vanish
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemIsom
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

private theorem crd_toLin_map_eq_mulVec_crd {D : D7} (X : HidaSetting D) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
    (y : (VS D).V) : X.crd (Matrix.toLin X.bas X.bas (M.map X.ιE) y) = M *ᵥ X.crd y := by
  have h := LinearMap.toMatrix_mulVec_repr X.bas X.bas (Matrix.toLin X.bas X.bas (M.map X.ιE)) y
  rw [LinearMap.toMatrix_toLin] at h
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, ← h, Matrix.mulVec, dotProduct,
    Matrix.map_apply, map_sum, map_mul, RingEquiv.symm_apply_apply]

theorem memIsomOf_holds : MemIsomOf := by
  intro D X g hg
  let A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E := (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  let B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
    ((g⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  have hinj : ∀ y y' : (VS D).V, X.crd y = X.crd y' → y = y' := by
    intro y y' h
    apply X.bas.repr.injective
    ext i
    have := congrFun h i
    simpa [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf] using this
  let n : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
    LinearEquiv.ofLinear (Matrix.toLin X.bas X.bas (A.map X.ιE)) (Matrix.toLin X.bas X.bas (B.map X.ιE))
      (LinearMap.ext fun y => hinj _ _ (by
        rw [LinearMap.comp_apply, crd_toLin_map_eq_mulVec_crd, crd_toLin_map_eq_mulVec_crd, Matrix.mulVec_mulVec]
        simp [A, B]))
      (LinearMap.ext fun y => hinj _ _ (by
        rw [LinearMap.comp_apply, crd_toLin_map_eq_mulVec_crd, crd_toLin_map_eq_mulVec_crd, Matrix.mulVec_mulVec]
        simp [A, B]))
  have hn : ∀ y, X.crd (n y) = A *ᵥ X.crd y := fun y => crd_toLin_map_eq_mulVec_crd X A y
  refine ⟨n, ?_, hn⟩
  intro x y
  rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X (n x) (n y), ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y,
    hn, hn, Formalism.L2.SG.PoincareInHH.Cut.hform_mulVec _ _ _ hg]

end Formalism.L2.SG.TermOp.Vanish
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemLat
section
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped Classical

namespace Formalism.L2.SG.Pf.RCoc

open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

variable {D : D7} (X : HidaSetting D)

theorem isInt_symm {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (X.ιE.symm x) :=
  hx.map (RingHom.toIntAlgHom (X.ιE.symm : D.host.E →+* X.B.I.E))

theorem isInt_fwd {x : X.B.I.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (X.ιE x) :=
  hx.map (RingHom.toIntAlgHom (X.ιE : X.B.I.E →+* D.host.E))

theorem natAbs_sq_cast {K : Type*} [Ring K] (z : ℤ) : (((z.natAbs ^ 2 : ℕ)) : K) = (z : K) * (z : K) := by
  rw [← Int.cast_natCast, Nat.cast_pow, Int.natCast_natAbs, sq_abs, sq, Int.cast_mul]

theorem crd_sub_lat (a b : (VS D).V) : X.crd (a - b) = X.crd a - X.crd b := by
  first
    | exact Formalism.L2.SG.Pf.Vanish2.crd_sub' (X := X) a b
    | exact map_sub _ a b
    | (funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf])

theorem repr_crd (a : (VS D).V) (i : Fin X.B.I.n) : X.bas.repr a i = X.ιE (X.crd a i) := by
  simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

theorem lat_pres (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E, IntDiv c (G - 1) →
      ∀ g : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ y, X.crd (g y) = G *ᵥ X.crd y) → ∀ y ∈ Λ, g y ∈ Λ := by
  obtain ⟨d, hd0, hd⟩ := Formalism.HermitianLatticesTheory.majLattice_exists_d X.bas Λ hΛ.fg
  have hc : ∀ i, ∃ c : ℤ, c ≠ 0 ∧ c • X.bas i ∈ Λ := fun i =>
    Formalism.HermitianLatticesTheory.majLattice_exists_c Λ hΛ.span_eq_top (X.bas i)
  choose c hc0 hcm using hc
  set C : ℤ := ∏ i, c i with hC
  have hCm : ∀ i, (C * C) • X.bas i ∈ Λ := by
    intro i
    have e : C = (∏ j ∈ Finset.univ.erase i, c j) * c i := by
      rw [hC, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    have h1 : C • X.bas i ∈ Λ := by
      rw [e, mul_smul]
      exact zsmul_mem (hcm i) _
    rw [mul_smul]
    exact zsmul_mem h1 _
  have hC0 : C ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hc0 i
  refine ⟨d.natAbs ^ 2 * C.natAbs ^ 2, ?_, ?_⟩
  · have h1 : 0 < d.natAbs := Int.natAbs_pos.2 hd0
    have h2 : 0 < C.natAbs := Int.natAbs_pos.2 hC0
    have := Nat.mul_pos (pow_pos h1 2) (pow_pos h2 2)
    omega
  rintro G ⟨A, hA, hGA⟩ g hg y hy
  set v := A *ᵥ X.crd y with hv
  have hw : X.crd (g y - y) = ((d.natAbs ^ 2 * C.natAbs ^ 2 : ℕ) : X.B.I.E) • v := by
    rw [crd_sub_lat, hg, ← Matrix.one_mulVec (X.crd y), Matrix.mulVec_mulVec, Matrix.mul_one,
      ← Matrix.sub_mulVec, hGA, Matrix.smul_mulVec]
  have hvi : ∀ i, IsIntegral ℤ (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i) := by
    intro i
    rw [hv, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine IsIntegral.sum _ fun j _ => ?_
    have e : ((d.natAbs ^ 2 : ℕ) : X.B.I.E) * (A i j * X.crd y j) =
        A i j * X.ιE.symm ((d : D.host.E) * ((d : D.host.E) * X.bas.repr y j)) := by
      rw [natAbs_sq_cast]
      simp only [HidaSetting.crd, crdOf, map_mul, map_intCast]
      ring
    rw [e]
    exact (hA i j).mul (isInt_symm X ((isInt_intCast d).mul (hd y hy j)))
  choose r hr using fun i => (⟨⟨X.ιE (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i), isInt_fwd X (hvi i)⟩, rfl⟩ :
    ∃ r : 𝓞 D.host.E, (r : D.host.E) = X.ιE (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i))
  have hsum : g y - y = ∑ i, r i • ((C * C) • X.bas i) := by
    conv_lhs => rw [← X.bas.sum_repr (g y - y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repr_crd, hw, Pi.smul_apply, smul_eq_mul, ← algebraMap_smul D.host.E (r i), ← Int.cast_smul_eq_zsmul D.host.E,
      smul_smul]
    congr 1
    show _ = (r i : D.host.E) * _
    rw [hr, Nat.cast_mul, mul_assoc, mul_comm, map_mul, map_mul, map_natCast, natAbs_sq_cast]
    simp only [map_mul, map_natCast]
    push_cast
    ring
  have hmem : g y - y ∈ Λ := by
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hCm i)
  have e : g y = y + (g y - y) := by abel
  rw [e]
  exact Λ.add_mem hy hmem

theorem lat_den_two {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (P : Matrix α β X.B.I.E) (Q : Matrix γ δ X.B.I.E) :
    ∃ m : ℕ, 0 < m ∧ IntDiv 1 ((m : X.B.I.E) • P) ∧ IntDiv 1 ((m : X.B.I.E) • Q) := by
  have hint : ∀ k : ℕ, IsIntegral ℤ ((k : X.B.I.E)) := fun k => by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ X.B.I.E (k : ℤ)))
  obtain ⟨d1, hd1, A, hA, hAe⟩ := exists_den (fun x => Formalism.L2.SG.Pf.nt_int_mul_of X.B.I x) P
  obtain ⟨d2, hd2, B, hB, hBe⟩ := exists_den (fun x => Formalism.L2.SG.Pf.nt_int_mul_of X.B.I x) Q
  refine ⟨d1 * d2, Nat.mul_pos hd1 hd2, ⟨(d2 : X.B.I.E) • A, fun i j => ?_, ?_⟩,
    ⟨(d1 : X.B.I.E) • B, fun i j => ?_, ?_⟩⟩
  · simpa [Matrix.smul_apply, smul_eq_mul] using (hint d2).mul (hA i j)
  · rw [Nat.cast_mul, mul_comm, mul_smul, hAe]
    simp
  · simpa [Matrix.smul_apply, smul_eq_mul] using (hint d1).mul (hB i j)
  · rw [Nat.cast_mul, mul_smul, hBe]
    simp

theorem lat_gE_sub_one (Z : Matrix (Kap X) (Kap X) X.B.I.E) :
    Formalism.L2.SG.Pf.UnipB.gE X Z - 1 = Bm X * (cay (N0 D) Z - 1) * Bm' X := by
  show Bm X * cay (N0 D) Z * Bm' X - 1 = Bm X * (cay (N0 D) Z - 1) * Bm' X
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Bm_mul_Bm']

theorem lat_gE_intDiv (mB : ℕ) (hB : IntDiv 1 ((mB : X.B.I.E) • Bm X)) (hB' : IntDiv 1 ((mB : X.B.I.E) • Bm' X))
    (c : ℕ) (A : Matrix (Kap X) (Kap X) X.B.I.E) (hA : ∀ i j, IsIntegral ℤ (A i j))
    (Z : Matrix (Kap X) (Kap X) X.B.I.E) (hZ : Z = ((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A) :
    IntDiv (2 * c) (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) := by
  subst hZ
  have hh : (⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A) = ((c * mB ^ 2 : ℕ) : X.B.I.E) • A := by
    rw [smul_smul]
    congr 1
    rw [show ((2 * c * mB ^ 2 : ℕ) : X.B.I.E) = 2 * ((c * mB ^ 2 : ℕ) : X.B.I.E) by push_cast; ring,
      ← mul_assoc, invOf_mul_self, one_mul]
  have hAi : IntDiv 1 A := ⟨A, hA, by simp⟩
  have hhalf : IntDiv 1 ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A)) := by
    rw [hh]
    refine ⟨((c * mB ^ 2 : ℕ) : X.B.I.E) • A, fun i j => ?_, by simp⟩
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (isInt_natCast _).mul (hA i j)
  have hgeo : IntDiv 1 (geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))) := by
    unfold geo
    refine intDiv_sum fun j _ => ?_
    have := intDiv_pow hhalf j
    rwa [one_pow] at this
  have hP := intDiv_mul (intDiv_mul hB (intDiv_mul hAi hgeo)) hB'
  rw [show (1 * (1 * 1) * 1 : ℕ) = 1 by norm_num] at hP
  obtain ⟨W, hW, hWe⟩ := hP
  refine ⟨W, hW, ?_⟩
  rw [lat_gE_sub_one]
  unfold cay
  rw [add_sub_cancel_left]
  have e : Bm X * ((((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A) *
      geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))) * Bm' X =
      ((2 * c : ℕ) : X.B.I.E) • (((mB : X.B.I.E) • Bm X) *
        (A * geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))) * ((mB : X.B.I.E) • Bm' X)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [e, hWe, Nat.cast_one, one_smul]

end Formalism.L2.SG.Pf.RCoc

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Pf.RCoc Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

theorem memLatOf_holds (D : D7) (X : HidaSetting D) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ (Z : Matrix (Kap X) (Kap X) X.B.I.E) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
      InPat (lvk X) 1 Z → (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Z = (d : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) →
      (∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y) → Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
  obtain ⟨c, hc, H⟩ := lat_pres X Λ hΛ
  obtain ⟨mB, hmB, hB, hB'⟩ := lat_den_two X (Bm X) (Bm' X)
  refine ⟨2 * c * mB ^ 2, Nat.mul_pos (Nat.mul_pos two_pos hc) (pow_pos hmB 2), fun Z n hZ hA hn => ?_⟩
  obtain ⟨A, hA⟩ := hA
  have hAi : ∀ i j, IsIntegral ℤ ((A.map (fun a => (a : X.B.I.E))) i j) := fun i j => (A i j).isIntegral_coe
  have h1 : IntDiv c (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) := by
    have := lat_gE_intDiv X mB hB hB' c _ hAi Z hA
    exact intDiv_dvd (d := 2) (by rwa [mul_comm c 2])
  have h2 : IntDiv c (Formalism.L2.SG.Pf.UnipB.gE X (-Z) - 1) := by
    have hneg : -Z = ((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • (-(A.map (fun a => (a : X.B.I.E)))) := by
      rw [hA, smul_neg]
    have := lat_gE_intDiv X mB hB hB' c _ (fun i j => (hAi i j).neg) (-Z) hneg
    exact intDiv_dvd (d := 2) (by rwa [mul_comm c 2])
  have hinv : Formalism.L2.SG.Pf.UnipB.gE X (-Z) * Formalism.L2.SG.Pf.UnipB.gE X Z = 1 := gE_mul X le_rfl hZ
  have hn' : ∀ y, X.crd (n.symm y) = Formalism.L2.SG.Pf.UnipB.gE X (-Z) *ᵥ X.crd y := by
    intro y
    conv_rhs => rw [← n.apply_symm_apply y, hn, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [Formalism.L2.SG.Pf.gmap_eq_iff]
  intro x
  constructor
  · intro hx
    have := H _ h2 n.symm.toLinearMap hn' (n x) hx
    simpa using this
  · intro hx
    exact H _ h1 n.toLinearMap hn x hx

end Formalism.L2.SG.TermOp.Vanish
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemPt
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

theorem memPtOf_holds : MemPtOf := by
  intro D X Z n hni hn
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hni
  refine ⟨x, hx, fun v => ?_⟩
  obtain ⟨M', -, h1, -, h3⟩ := hx
  have hM : (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = gE X Z := by
    apply Matrix.ext_of_mulVec_single
    intro i
    obtain ⟨y, hy⟩ := Formalism.L2.SG.Pf.crd_surj X (Pi.single i 1)
    rw [← hy, ← h3, hn]
  unfold Mv
  rw [h1 v, hM, gE_real]
  simp only [← Matrix.mul_assoc, Bv'_mul_Bv, Matrix.one_mul]
  rw [Matrix.mul_assoc, Bv'_mul_Bv, Matrix.mul_one, cay_map]

end Formalism.L2.SG.TermOp.Vanish
end
end

