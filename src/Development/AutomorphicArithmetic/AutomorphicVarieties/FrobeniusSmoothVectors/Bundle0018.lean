module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrNorm
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {C C' : Type} [CommRing C] [CommRing C']

private theorem conj_left {G : Type} [Group G] (h : GL (Fin n) C)
    (r : G →* GG (m := n) (R := C)) (s : G) :
    (conjBy h r s).left = h * (r s).left * sgnAct n C (r s).right h⁻¹ := by
  simp [conjBy, GG.ofGL, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.mul_right, mul_assoc]

private theorem conj_right {G : Type} [Group G] (h : GL (Fin n) C)
    (r : G →* GG (m := n) (R := C)) (s : G) :
    (conjBy h r s).right = (r s).right := by
  simp [conjBy, GG.ofGL, MulAut.conj_apply, SemidirectProduct.mul_right]

private theorem conj_mat {G : Type} [Group G] (h : GL (Fin n) C)
    (r : G →* GG (m := n) (R := C)) (s : G) (hs : (r s).right = 1) :
    (conjBy h r s).mat = (h : Matrix (Fin n) (Fin n) C) * (r s).mat *
      ((h⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) := by
  unfold GG.mat
  rw [conj_left, hs, sgnAct_one, Units.val_mul, Units.val_mul]

private theorem conj_mul {G : Type} [Group G] (h h' : GL (Fin n) C)
    (r : G →* GG (m := n) (R := C)) :
    conjBy (h * h') r = conjBy h (conjBy h' r) := by
  apply MonoidHom.ext
  intro s
  simp [conjBy, MulAut.conj_apply, _root_.mul_inv_rev, mul_assoc]

private theorem frame_right_eq_one_of_G0 (B : Box F n C) (s : F.G0) : (B.r s).right = 1 := by
  exact (B.nu s).trans (MonoidHom.mem_ker.mp s.2)

private noncomputable def cj (h : GL (Fin n) C) (B : Box F n C) : Box F n C where
  r := conjBy h B.r
  nu s := (conj_right h B.r s).trans (B.nu s)
  g v := B.g v * h⁻¹
  tri v s := by
    have e : B.g v * h⁻¹ * (conjBy h B.r (F.loc v s)).left * (B.g v * h⁻¹)⁻¹ =
        B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ := by
      have : (B.r (F.loc v s)).right = 1 := frame_right_eq_one_of_G0 B (F.loc0 v s)
      rw [conj_left, this, sgnAct_one]
      group
    have e' := congrArg Units.val e
    simp only [Units.val_mul] at e'
    have := B.tri v s
    unfold GG.mat at this ⊢
    rw [← e'] at this
    simpa only [Units.val_mul] using this

private theorem cj_map (f : C →+* C') (h : GL (Fin n) C) (B : Box F n C)
    (hh : (h : Matrix (Fin n) (Fin n) C).map f = 1) : (cj h B).map f = B.map f := by
  have hh' : Matrix.GeneralLinearGroup.map f h = 1 := Units.ext (by simpa using hh)
  have hg : GG.map f (GG.ofGL h) = 1 := by
    simp [GG.map, GG.ofGL, hh']
  apply Box.ext
  · apply MonoidHom.ext
    intro s
    show GG.map f (conjBy h B.r s) = GG.map f (B.r s)
    simp [conjBy, MulAut.conj_apply, map_mul, map_inv, hg]
  · funext v
    show Matrix.GeneralLinearGroup.map f (B.g v * h⁻¹) = Matrix.GeneralLinearGroup.map f (B.g v)
    simp [map_mul, map_inv, hh']

private theorem cj_cont (hd : IsOpen (F.del.ker : Set F.Γ)) (I : Ideal C) (h : GL (Fin n) C) (B : Box F n C)
    (hB : B.Cont I) : (cj h B).Cont I := by
  intro i j N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hdel : ∀ᶠ y in nhds x, F.del y = F.del x := by
    have hopen : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (F.del.ker : Set F.Γ)) :=
      hd.preimage (continuous_const.mul continuous_id)
    filter_upwards [hopen.mem_nhds (by simp)] with y hy
    have e : F.del (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at e
    exact e.symm
  have hM : ∀ᶠ y in nhds x, ∀ a b : Fin n,
      Ideal.Quotient.mk (I ^ N) ((B.r y).mat a b) = Ideal.Quotient.mk (I ^ N) ((B.r x).mat a b) := by
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    exact (hB a b N).eventually_eq x
  filter_upwards [hdel, hM] with y hy hMy
  show Ideal.Quotient.mk (I ^ N) ((conjBy h B.r y).mat i j) = Ideal.Quotient.mk (I ^ N) ((conjBy h B.r x).mat i j)
  simp only [GG.mat] at hMy ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [conj_left, B.nu, hy, Units.val_mul, Matrix.mul_apply, map_sum, map_mul, hMy]

private theorem of_unique {B : Box F n C} {ρ ρ' : NRep F n C} (h : B.Of ρ) (h' : B.Of ρ') : ρ = ρ' := by
  have e : ρ.r = ρ'.r := MonoidHom.ext fun s => (h.res s).symm.trans (h'.res s)
  apply NRep.ext e
  funext v i
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [← h.psi, ← h'.psi, e]

private theorem star_mat (hc : F.del F.c = -1) (B : Box F n C) (h1 : (B.r F.c).mat = 1) (g : F.G0) :
    (B.r (F.star g)).mat = Jmat (R := C) n * (B.r g).matᵀ * Jmat (R := C) n := by
  have t1 : theta (1 : GL (Fin n) C) = 1 := by
    simpa [sgnAct_neg_one] using map_one (sgnAct (m := n) (R := C) (-1))
  have hX : B.r F.c = ⟨1, -1⟩ := SemidirectProduct.ext (Units.ext (by simpa [GG.mat] using h1)) ((B.nu _).trans hc)
  have hY : B.r (g : F.Γ) = ⟨(B.r g).left, 1⟩ := SemidirectProduct.ext rfl (frame_right_eq_one_of_G0 B g)
  rw [show ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ from rfl, map_mul, map_mul, map_inv, map_inv, hX, hY]
  simp [GG.mat, SemidirectProduct.mul_left, SemidirectProduct.inv_left, map_inv, sgnAct_neg_one, sgnAct_one, theta_inv_val]
  rw [t1, t1, Units.val_one, mul_one, ← Matrix.coe_units_inv, theta_inv_val]

end SlopeTestRemainingChoices

end UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_norm :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (ρ : NRep F n C) (B' : Box F n C'), maximalIdeal C' * RingHom.ker p = ⊥ → (ρ.bar O).Good → (B'.map (p : C' →+* C)).Of ρ → B'.Cont (maximalIdeal C') → ∃ (h : GL (Fin n) C') (ρ' : NRep F n C'), (h : Matrix (Fin n) (Fin n) C').map p = 1 ∧ ρ'.map (p : C' →+* C) = ρ ∧ ρ'.Cont (maximalIdeal C') ∧ (conjBy h B'.r F.c).mat = 1 ∧ ∀ s : F.G0, (conjBy h B'.r s).mat = ρ'.r s := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p ρ B' hmk hgood hof hcont
  have hkp : RingHom.ker p ≤ maximalIdeal C' := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [← res_eq_zero_iff O C', ← res_map p x, hx, map_zero]
  have hmat : ∀ (B : Box F n C') (s : F.Γ), ((B.map (p : C' →+* C)).r s).mat = (B.r s).mat.map p := fun B s => rfl
  have hx1 : (B'.r F.c).mat.map p = 1 := by
    rw [← hmat]
    exact hof.atc
  obtain ⟨h1, hh1, hc1⟩ := pr_norm1 O C' C p n (B'.r F.c) hmk hkp hgood.two
    (by rw [← map_mul, hF.c_sq, map_one]) ((B'.nu _).trans hF.del_c) hx1
  set B1 := cj h1 B' with hB1
  have hB1c : (B1.r F.c).mat = 1 := hc1
  have hB1map : B1.map (p : C' →+* C) = B'.map (p : C' →+* C) := cj_map _ h1 B' hh1
  have hB1cont : B1.Cont (maximalIdeal C') := cj_cont hF.del_open _ h1 B' hcont
  have hstar : ∀ g : F.G0, (B1.r (F.star g)).mat =
      Jmat (R := C') n * (B1.r g).matᵀ * Jmat (R := C') n :=
    star_mat hF.del_c B1 hB1c
  set Z := (B1.r F.g0).mat - (B1.r (F.star F.g0)).mat with hZ
  have hJ : ∀ X : Matrix (Fin n) (Fin n) C', Jmat (R := C') n * (Jmat (R := C') n * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
  have hθ : thetaLie Z = Z := by
    rw [hZ, hstar]
    simp only [thetaLie, Matrix.transpose_sub, Matrix.transpose_mul, Jmat_transpose, Matrix.transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hJ, Jmat_mul_Jmat, Matrix.mul_one]
    abel
  have hZp : Z.map p = ρ.r F.g0 - ρ.r (F.star F.g0) := by
    rw [hZ, Matrix.map_sub _ (fun a b => map_sub p a b), ← hmat, ← hmat, hB1map, hof.res, hof.res]
  have hoff : ∀ i j : Fin n, i ≠ j → p (Z i j) = 0 := by
    intro i j hij
    have e := congrFun (congrFun hZp i) j
    rw [Matrix.map_apply] at e
    rw [e]
    exact ρ.diag i j hij
  have hdist : ∀ i j : Fin n, i ≠ j → res O C' (Z i i) ≠ res O C' (Z j j) := by
    intro i j hij
    have e : ∀ a, p (Z a a) = (ρ.r F.g0 - ρ.r (F.star F.g0)) a a := fun a => by
      rw [← hZp, Matrix.map_apply]
    rw [← res_map p, ← res_map p, e i, e j]
    convert hgood.zd i j hij using 1 <;> simp [NRep.bar, NRep.map]
  obtain ⟨h2', hh2, hθ2, hdiag2⟩ := pr_norm2 O C' C p n Z hmk hkp hθ hoff hdist
  set B2 := cj h2' B1 with hB2
  have hB2c : (B2.r F.c).mat = 1 := by
    show (conjBy h2' B1.r F.c).mat = 1
    have hl : (B1.r F.c).left = 1 := Units.ext hB1c
    unfold GG.mat
    rw [conj_left, B1.nu, hF.del_c, hl, mul_one, map_inv, sgnAct_neg_one, hθ2, mul_inv_cancel, Units.val_one]
  have hB2diag : ∀ i j : Fin n, i ≠ j → ((B2.r F.g0).mat - (B2.r (F.star F.g0)).mat) i j = 0 := by
    intro i j hij
    have e1 := conj_mat h2' B1.r (F.g0 : F.Γ) (frame_right_eq_one_of_G0 B1 F.g0)
    have e2 := conj_mat h2' B1.r ((F.star F.g0 : F.G0) : F.Γ) (frame_right_eq_one_of_G0 B1 (F.star F.g0))
    show ((conjBy h2' B1.r F.g0).mat - (conjBy h2' B1.r (F.star F.g0)).mat) i j = 0
    rw [e1, e2, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact hdiag2 i j hij
  have hB2cont : B2.Cont (maximalIdeal C') := cj_cont hF.del_open _ h2' B1 hB1cont
  obtain ⟨ρ', hof', hcont'⟩ := pr_ofbox hF C' (maximalIdeal C') B2 hB2c hB2diag hB2cont
  refine ⟨h2' * h1, ρ', ?_, ?_, hcont', ?_, ?_⟩
  · show ((h2' : Matrix (Fin n) (Fin n) C') * h1).map (p : C' →+* C) = 1
    rw [Matrix.map_mul]
    exact (congrArg₂ (· * ·) hh2 hh1).trans (Matrix.one_mul 1)
  · have e := hof'.map (p : C' →+* C)
    rw [show B2.map (p : C' →+* C) = B'.map (p : C' →+* C) from (cj_map _ h2' B1 hh2).trans hB1map] at e
    exact of_unique e hof
  · rw [conj_mul]
    exact hB2c
  · intro s
    rw [conj_mul]
    exact hof'.res s
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSetlift
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ac_const {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (c : R) :
    AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := fun N => by
  simp only [map_mul]
  exact (hf N).mul (hg N)

private theorem ac_sum {Γ R ι : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} (S : Finset ι)
    {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) : AdicCont I fun s => ∑ i ∈ S, f i s := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) (∑ i ∈ S, f i s)) = ∑ i ∈ S, fun s => Ideal.Quotient.mk (I ^ N) (f i s) := by
    funext s
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_apply]
  rw [e]
  exact Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb) (IsLocallyConstant.const 0) (fun i _ => hf i N)

private theorem gl_lift {n : ℕ} (O : Type) [CommRing O] [IsLocalRing O] (C' : Type) [CommRing C'] [Algebra O C']
    [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (hp : Function.Surjective p)
    (hk : maximalIdeal C' * RingHom.ker p = ⊥) (Γ : Type) [TopologicalSpace Γ] (x : Γ → GL (Fin n) C)
    (hx : ∀ i j, AdicCont (maximalIdeal C) fun s => x s i j) :
    ∃ y : Γ → GL (Fin n) C', (∀ i j, AdicCont (maximalIdeal C') fun s => y s i j) ∧
      (∀ s, GeneralLinearGroup.map (p : C' →+* C) (y s) = x s) ∧
      ∀ i j, (∀ s, x s i j = 0) → ∀ s, y s i j = 0 := by
  classical
  have hloc : ∀ a : C', IsUnit (p a) → IsUnit a := by
    intro a ha
    by_contra hna
    obtain ⟨b, hb⟩ := hp (↑ha.unit⁻¹ : C)
    have hK : a * b - 1 ∈ RingHom.ker (p : C' →+* C) := by
      rw [RingHom.mem_ker]
      show p (a * b - 1) = 0
      rw [map_sub, map_mul, map_one, hb, IsUnit.mul_val_inv, sub_self]
    have hKm : RingHom.ker (p : C' →+* C) ≤ maximalIdeal C' := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    have ham : a ∈ maximalIdeal C' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hna
    have h1 : (1 : C') ∈ maximalIdeal C' := by
      have h2 := sub_mem (Ideal.mul_mem_right b _ ham) (hKm hK)
      simpa using h2
    exact (maximalIdeal.isMaximal C').ne_top ((Ideal.eq_top_iff_one _).2 h1)
  let Y : Fin n → Fin n → Γ → C' := fun i j =>
    if ∀ s, x s i j = 0 then fun _ => 0 else Classical.choose (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))
  have hYc : ∀ i j, AdicCont (maximalIdeal C') (Y i j) := by
    intro i j
    by_cases h : ∀ s, x s i j = 0
    · simp only [Y, if_pos h]
      exact fun _ => IsLocallyConstant.const _
    · simp only [Y, if_neg h]
      exact (Classical.choose_spec (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))).1
  have hYp : ∀ i j s, p (Y i j s) = x s i j := by
    intro i j s
    by_cases h : ∀ s, x s i j = 0
    · simp only [Y, if_pos h, map_zero]
      exact (h s).symm
    · simp only [Y, if_neg h]
      exact (Classical.choose_spec (pr_sec O C' C p hp hk Γ (fun s => x s i j) (hx i j))).2 s
  have hY0 : ∀ i j, (∀ s, x s i j = 0) → ∀ s, Y i j s = 0 := by
    intro i j h s
    simp only [Y, if_pos h]
  let M : Γ → Matrix (Fin n) (Fin n) C' := fun s => Matrix.of fun i j => Y i j s
  have hMp : ∀ s, (M s).map p = (x s : Matrix (Fin n) (Fin n) C) := by
    intro s
    ext i j
    exact hYp i j s
  have hdet : ∀ s, IsUnit (M s).det := by
    intro s
    apply hloc
    have e : p (M s).det = ((M s).map p).det := RingHom.map_det (p : C' →+* C) (M s)
    rw [e, hMp]
    exact Matrix.isUnits_det_units (x s)
  refine ⟨fun s => Matrix.nonsingInvUnit (M s) (hdet s), fun i j => hYc i j, fun s => ?_, fun i j h s => hY0 i j h s⟩
  apply Units.ext
  exact hMp s

theorem UpperTheory.V.Fr.pr_setlift :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C), Function.Surjective p → maximalIdeal C' * RingHom.ker p = ⊥ → B.Cont (maximalIdeal C) → Nonempty (SetLift p B) := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B hp hk hcont
  obtain ⟨r, hrc, hrm, -⟩ := gl_lift O C' C p hp hk F.Γ (fun s => (B.r s).left) (fun i j => hcont i j)
  have hg : ∀ v, ∃ a : GL (Fin n) C', GeneralLinearGroup.map (p : C' →+* C) a = B.g v := by
    intro v
    obtain ⟨y, -, hy, -⟩ := gl_lift O C' C p hp hk Unit (fun _ => B.g v)
      (fun i j N => IsLocallyConstant.of_constant _ (fun _ _ => rfl))
    exact ⟨y (), hy ()⟩
  have ht : ∀ v, ∃ y : F.Gv v → GL (Fin n) C', (∀ i j, AdicCont (maximalIdeal C') fun s => y s i j) ∧
      (∀ s, GeneralLinearGroup.map (p : C' →+* C) (y s) = B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹) ∧
      ∀ s, UpT (y s : Matrix (Fin n) (Fin n) C') := by
    intro v
    have hM : ∀ a b, AdicCont (maximalIdeal C) fun s : F.Gv v => (B.r (F.loc v s)).mat a b :=
      fun a b N => (hcont a b N).comp_continuous (continuous_subtype_val.comp (hF.loc_cont v))
    have hx : ∀ i j, AdicCont (maximalIdeal C) fun s : F.Gv v => ((B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) i j := by
      intro i j
      simp only [Units.val_mul, Matrix.mul_apply]
      exact ac_sum _ (f := fun q s => (∑ a, (B.g v : Matrix (Fin n) (Fin n) C) i a * (B.r (F.loc v s)).mat a q) * ((B.g v)⁻¹ : GL (Fin n) C) q j)
        fun q => ac_mul (ac_sum _ (f := fun a s => (B.g v : Matrix (Fin n) (Fin n) C) i a * (B.r (F.loc v s)).mat a q)
          fun a => ac_mul (ac_const _ _) (hM a q)) (ac_const _ _)
    obtain ⟨y, hyc, hym, hy0⟩ := gl_lift O C' C p hp hk (F.Gv v) _ hx
    refine ⟨y, hyc, hym, fun s i j hij => hy0 i j (fun s' => B.tri v s' i j hij) s⟩
  choose g hgm using hg
  choose t htc htm htt using ht
  exact ⟨⟨r, hrc, hrm, g, hgm, t, htc, htt, htm⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrpOfMemSucc
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prp_of_mem {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K)
    (hX : X ∈ adp K j) : ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) = X := by
  ext a b
  show (if pw a b = j then X a b else 0) = X a b
  split_ifs with h
  · rfl
  · exact (hX a b h).symm

private theorem prp_of_mem_succ {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K)
    (hX : X ∈ adp K (j + 1)) : ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) = 0 := by
  ext a b
  show (if pw a b = j then X a b else 0) = 0
  split_ifs with h
  · have hne : ∀ p q : ZMod 2, p = q → p ≠ q + 1 := by decide
    exact hX a b (hne _ _ h)
  · rfl

private theorem prp_add {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K) :
    X = ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) + (prp K (j + 1) X : adp K (j + 1)) := by
  ext a b
  show X a b = (if pw a b = j then X a b else 0) + (if pw a b = j + 1 then X a b else 0)
  have hc : ∀ p q : ZMod 2, (p = q ∧ p ≠ q + 1) ∨ (p ≠ q ∧ p = q + 1) := by decide
  rcases hc (pw a b) j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2, add_zero]
  · rw [if_neg h1, if_pos h2, zero_add]

theorem UpperTheory.V.Fr.ep_prp :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), (∀ j s X, prp K j (B.ad s X) = h.ad j s (prp K j X)) ∧ ∀ (j : ZMod 2) (χ : F.Γ → K), (∀ f : Matrix (Fin 3) (Fin 3) K →ₗ[K] K, (∀ g X, f (B.ad g X) = χ g * f X) → f = 0) → ∀ f : adp K j →ₗ[K] K, (∀ g X, f (h.ad j g X) = χ g * f X) → f = 0 := by
  intro l _ k _ F K _ h2 B π h
  have P1 : ∀ j s X, prp K j (B.ad s X) = h.ad j s (prp K j X) := by
    intro j s X
    apply Subtype.ext
    rw [Box.Ev.ad_apply]
    conv_lhs => rw [prp_add j X]
    rw [map_add (f := _), map_add (f := _), Submodule.coe_add,
      prp_of_mem j _ (h.stab j s (prp K j X).2),
      prp_of_mem_succ j _ (h.stab (j + 1) s (prp K (j + 1) X).2), add_zero]
  refine ⟨P1, ?_⟩
  intro j χ hχ f hf
  have hF := hχ (f.comp (prp K j)) (fun g X => by simp only [LinearMap.comp_apply, P1, hf])
  ext v
  have := LinearMap.congr_fun hF (v : Matrix (Fin 3) (Fin 3) K)
  have hv : prp K j (v : Matrix (Fin 3) (Fin 3) K) = v := Subtype.ext (prp_of_mem j _ v.2)
  simpa [hv] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ResDual
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem res_dual (O : Type) [CommRing O] [IsLocalRing O] [IsCO O (DualNumber (ResidueField O))]
    (x : DualNumber (ResidueField O)) : res O _ x = x.fst := by
  obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective x.fst
  have ha : (algebraMap O (DualNumber (ResidueField O)) o).fst = x.fst := by
    rw [← ho]
    first
      | rfl
      | rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, IsLocalRing.ResidueField.algebraMap_eq]
  have hfst : (x - algebraMap O _ o).fst = 0 := by
    rw [TrivSqZeroExt.fst_sub, ha, sub_self]
  have hsq : (x - algebraMap O _ o) * (x - algebraMap O _ o) = 0 := by
    ext
    · rw [TrivSqZeroExt.fst_mul, hfst, mul_zero, TrivSqZeroExt.fst_zero]
    · rw [TrivSqZeroExt.snd_mul, hfst, zero_smul, MulOpposite.op_zero, zero_smul, add_zero, TrivSqZeroExt.snd_zero]
  have hmem : x - algebraMap O _ o ∈ maximalIdeal (DualNumber (ResidueField O)) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h2 := hu.mul hu
    rw [hsq] at h2
    exact not_isUnit_zero h2
  have h0 := (res_eq_zero_iff O _ _).2 hmem
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h0
  rw [h0, ← ha]
  first
    | rfl
    | rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]

theorem UpperTheory.V.Fr.pr_dof :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ [IsCO O (DualNumber (ResidueField O))] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → ∀ (ρ' : NRep F n (DualNumber (ResidueField O))) (r' : F.Γ →* GG (m := n) (R := DualNumber (ResidueField O))), ρ'.Cont (maximalIdeal _) → ρ'.bar O = ρ.bar O → (∀ s, (r' s).right = F.del s) → (r' F.c).mat = 1 → (∀ s : F.G0, (r' s).mat = ρ'.r s) → ∃ D ∈ Tan O R, ∀ s, (r' s).mat.map TrivSqZeroExt.snd = B.tanCo O D s * ((B.bar O).r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ _ R _ _ _ ρ B hU hOf ρ' r' hc' hbar hnu hatc hres
  obtain ⟨g, hg, -⟩ := hU.univ _ ρ' hc' hbar
  have hfst : ∀ x, (g x).fst = res O R x := fun x => by
    rw [← res_dual O (g x), res_map]
  let Dd : R →ₗ[O] ResidueField O :=
    { toFun := fun x => (g x).snd
      map_add' := fun x y => by
        simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun a x => by
        simp only [map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
  have hDd : ∀ x, Dd x = (g x).snd := fun _ => rfl
  have hr : (Box.map (g : R →+* DualNumber (ResidueField O)) B).r = r' := by
    refine pr_ext hF _ _ _ (Box.nu _) hnu ?_ ?_
    · change (B.r F.c).mat.map g = (r' F.c).mat
      rw [hOf.atc, hatc]
      exact Matrix.map_one _ (map_zero g) (map_one g)
    · intro s
      change (B.r s).mat.map g = (r' s).mat
      rw [hOf.res]
      change (ρ.map (g : R →+* DualNumber (ResidueField O))).r s = (r' s).mat
      rw [hg, hres]
  refine ⟨Dd, ?_, fun s => ?_⟩
  · intro f h
    rw [hDd, hDd, hDd, map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]
  · rw [← hr]
    show ((B.r s).mat.map g).map TrivSqZeroExt.snd = ((B.r s).mat.map Dd * ((((Box.bar O B).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))) * ((((Box.bar O B).r s).left : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))
    rw [mul_assoc, Units.inv_mul, mul_one, Matrix.map_map]
    rfl
end

