module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem isInternal_congr {ι M σ σ' : Type} [DecidableEq ι] [AddCommMonoid M] [SetLike σ M]
    [AddSubmonoidClass σ M] [SetLike σ' M] [AddSubmonoidClass σ' M] (A : ι → σ) (A' : ι → σ')
    (h : ∀ i x, x ∈ A' i ↔ x ∈ A i) (hA : DirectSum.IsInternal A) : DirectSum.IsInternal A' := by
  let e : ∀ i, A' i ≃+ A i := fun i =>
    { toFun := fun x => ⟨x.1, (h i _).1 x.2⟩
      invFun := fun x => ⟨x.1, (h i _).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let E : DirectSum ι (fun i => A' i) ≃+ DirectSum ι (fun i => A i) := DFinsupp.mapRange.addEquiv e
  have hE : DirectSum.coeAddMonoidHom A' = (DirectSum.coeAddMonoidHom A).comp E.toAddMonoidHom := by
    refine DirectSum.addHom_ext fun i x => ?_
    have h1 : E (DirectSum.of (fun i => A' i) i x) = DirectSum.of (fun i => A i) i (e i x) :=
      DFinsupp.mapRange_single (hf := fun i => (e i).map_zero)
    show _ = DirectSum.coeAddMonoidHom A (E (DirectSum.of (fun i => A' i) i x))
    rw [h1, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    rfl
  unfold DirectSum.IsInternal
  rw [hE]
  exact hA.comp E.bijective

private theorem gr_transfer (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R)
    (hz : ∀ s, W.z s ∈ maximalIdeal R) (B A : Subalgebra O R) [Algebra B A]
    (halg : ∀ b : B, ((algebraMap B A b : A) : R) = b) (gr : ℤ → Submodule B A)
    (hB : ∀ y, y ∈ B ↔ y ∈ W.part 0) (hA : A = W.A) (hgr : ∀ j (a : A), a ∈ gr j ↔ (a : R) ∈ W.part j) :
    DirectSum.IsInternal gr ∧ SetLike.GradedMonoid gr ∧ gr 0 = 1 ∧ (∀ j, (gr j).FG) ∧ Algebra.FiniteType B A ∧
      IsNoetherianRing A := by
  subst hA
  obtain ⟨h1, h2, h3⟩ := gr_noeth O ℤ R W hz
  have h0 : ∀ a : W.A, a ∈ W.gr 0 → ∃ b : B, algebraMap B W.A b = a := fun a ha =>
    ⟨⟨a, (hB _).2 ha⟩, Subtype.ext (halg _)⟩
  refine ⟨isInternal_congr W.gr gr hgr (gr_internal O ℤ R W), ?_, ?_, fun j => ?_, ?_, h1⟩
  · exact
      { one_mem := (hgr _ _).2 (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
        mul_mem := fun _ _ _ _ ha hb => (hgr _ _).2 (SetLike.mul_mem_graded ((hgr _ _).1 ha) ((hgr _ _).1 hb)) }
  · ext a
    rw [Submodule.mem_one, hgr]
    refine ⟨h0 a, ?_⟩
    rintro ⟨b, rfl⟩
    rw [halg]
    exact (hB _).1 b.2
  · obtain ⟨s, hs, hs'⟩ := h3 j
    refine ⟨s, le_antisymm (Submodule.span_le.2 fun a ha => (hgr _ _).2 (hs a ha)) fun a ha => ?_⟩
    have ha' : a ∈ W.gr j := (hgr _ _).1 ha
    rw [hs'] at ha'
    refine Submodule.mul_induction_on ha' (fun x hx y hy => ?_) fun x y hx hy => add_mem hx hy
    obtain ⟨b, rfl⟩ := h0 x hx
    rw [← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy =>
      obtain ⟨b, hb⟩ := h0 _ (SetLike.algebraMap_mem_graded W.gr c)
      rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hy
  · obtain ⟨s, hs⟩ := h2.out
    refine ⟨⟨s, ?_⟩⟩
    rw [eq_top_iff]
    intro a ht
    clear ht
    have ha : a ∈ Algebra.adjoin (W.gr 0) (s : Set W.A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap r =>
      obtain ⟨b, hb⟩ := h0 r.1 r.2
      have : algebraMap (W.gr 0) W.A r = algebraMap B W.A b := hb.symm
      rw [this]
      exact Subalgebra.algebraMap_mem _ b
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb

theorem UpperTheory.V.Fr.gr_A :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, DirectSum.IsInternal S.gr ∧ SetLike.GradedMonoid S.gr ∧ S.gr 0 = 1 ∧ (∀ j, (S.gr j).FG) ∧ Algebra.FiniteType S.B S.A ∧ IsNoetherianRing S.A ∧ ∀ g i j, S.u.r g i j ∈ S.gr (w n i - w n j) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, hr, hB, hA, hgr⟩ := UpperTheory.V.Fr.wpres hF hn S
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := gr_transfer O S.R W hz S.B S.A (fun _ => rfl) S.gr hB hA hgr
  exact ⟨h1, h2, h3, h4, h5, h6, fun g i j => (hgr _ _).2 (hr g i j)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : UpperTheory.V.Fr.Frame l (ResidueField O)} {n : ℕ}
  (S : Space O F n)

end

theorem UpperTheory.V.Fr.cont_u :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, S.u.Cont S.x0 ∧ (∀ i, AdicCont S.mB fun g => S.aB g i) ∧ (∀ v i, AdicCont S.mB (S.ψB v i)) ∧ ∀ j (N : ℕ), ∃ M : ℕ, ∀ a ∈ S.gr j, (a : S.R) ∈ maximalIdeal S.R ^ M → a ∈ S.mB ^ N • S.gr j := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, hr, hB, hA, hgr⟩ := wpres hF hn S
  have hAW : ∀ (j : ℤ) (q : S.R), q ∈ W.part j → q ∈ S.A := by
    intro j q hq
    rw [hA]
    exact Submodule.mem_iSup_of_mem j hq
  have hmulB : ∀ (N : ℕ) (Q : Submodule O S.R),
      (∀ y ∈ Q, ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N) →
      ∀ y ∈ Q * W.part 0, ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N := by
    intro N Q hQ y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro p hp q hq
      obtain ⟨p', rfl, hp'⟩ := hQ p hp
      have hq0 : q ∈ S.B := (hB q).2 hq
      exact ⟨p' * ⟨q, hq0⟩, rfl, Ideal.mul_mem_right _ _ hp'⟩
    · rintro x z ⟨x', rfl, hx'⟩ ⟨z', rfl, hz'⟩
      exact ⟨x' + z', rfl, Ideal.add_mem _ hx' hz'⟩
  have hP : ∀ (N : ℕ) (y : S.R), y ∈ (W.part 0 ⊓ Submodule.restrictScalars O (maximalIdeal S.R)) ^ N →
      ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N := by
    intro N
    induction N with
    | zero =>
      intro y hy
      rw [pow_zero, Submodule.mem_one] at hy
      obtain ⟨o, rfl⟩ := hy
      exact ⟨algebraMap O S.B o, rfl, by simp⟩
    | succ N ih =>
      intro y hy
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro p hp q hq
        obtain ⟨p', rfl, hp'⟩ := ih p hp
        have hq0 : q ∈ S.B := (hB q).2 hq.1
        have hqm : (⟨q, hq0⟩ : S.B) ∈ S.mB := by
          show q ∈ maximalIdeal S.R
          exact hq.2
        refine ⟨p' * ⟨q, hq0⟩, rfl, ?_⟩
        rw [pow_succ]
        exact Ideal.mul_mem_mul hp' hqm
      · rintro x z ⟨x', rfl, hx'⟩ ⟨z', rfl, hz'⟩
        exact ⟨x' + z', rfl, Ideal.add_mem _ hx' hz'⟩
  have hT : ∀ (N : ℕ) (j : ℤ) (y : S.R),
      y ∈ (W.part 0 ⊓ Submodule.restrictScalars O (maximalIdeal S.R)) ^ N * W.part 0 * W.part j →
      ∃ a : S.A, (a : S.R) = y ∧ a ∈ S.mB ^ N • S.gr j ∧ a ∈ S.x0 ^ N := by
    intro N j y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro p hp q hq
      obtain ⟨b, rfl, hb⟩ := hmulB N _ (hP N) p hp
      have hqA : q ∈ S.A := hAW j q hq
      refine ⟨b • (⟨q, hqA⟩ : S.A), rfl, Submodule.smul_mem_smul hb ((hgr j ⟨q, hqA⟩).2 hq), ?_⟩
      have hib : S.inc b ∈ S.x0 ^ N := by
        rw [Space.x0, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hb
      show S.inc b * ⟨q, hqA⟩ ∈ S.x0 ^ N
      exact Ideal.mul_mem_right _ _ hib
    · rintro x z ⟨x', rfl, hx1, hx2⟩ ⟨z', rfl, hz1, hz2⟩
      exact ⟨x' + z', rfl, Submodule.add_mem _ hx1 hz1, Ideal.add_mem _ hx2 hz2⟩
  have hcA : ∀ {Γ : Type} [TopologicalSpace Γ] (j : ℤ) (f : Γ → S.A), (∀ g, (f g : S.R) ∈ W.part j) →
      AdicCont (maximalIdeal S.R) (fun g => (f g : S.R)) → AdicCont S.x0 f := by
    intro Γ _ j f hf hc N
    obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz j N
    have hcM := hc M
    rw [IsLocallyConstant.iff_eventually_eq] at hcM ⊢
    intro x
    filter_upwards [hcM x] with y hy
    rw [Ideal.Quotient.eq] at hy ⊢
    obtain ⟨a, ha, -, ha2⟩ := hT N j _ (hM ⟨Submodule.sub_mem _ (hf y) (hf x), hy⟩)
    have hax : f y - f x = a := Subtype.ext (by rw [ha]; rfl)
    rw [hax]
    exact ha2
  have hcB : ∀ {Γ : Type} [TopologicalSpace Γ] (f : Γ → S.B),
      AdicCont (maximalIdeal S.R) (fun g => (f g : S.R)) → AdicCont S.mB f := by
    intro Γ _ f hc N
    obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz 0 N
    have hcM := hc M
    rw [IsLocallyConstant.iff_eventually_eq] at hcM ⊢
    intro x
    filter_upwards [hcM x] with y hy
    rw [Ideal.Quotient.eq] at hy ⊢
    have hd : ((f y : S.R) - f x) ∈ W.part 0 := (hB _).1 (S.B.sub_mem (f y).2 (f x).2)
    obtain ⟨b, hb, hb2⟩ := hmulB N _ (hmulB N _ (hP N)) _ (hM ⟨hd, hy⟩)
    have hbx : f y - f x = b := Subtype.ext (by rw [hb]; rfl)
    rw [hbx]
    exact hb2
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, fun i => ?_, fun v i => ?_, fun j N => ?_⟩
  · exact hcA (w n i - w n j) (fun g => S.u.r g i j) (fun g => hr g i j) (S.lift.1.1 i j)
  · exact hcA 0 (fun g => (S.u.ψ v i g : S.A)) (fun g => (hB _).1 (S.ψB v i g).2) (S.lift.1.2 v i)
  · exact hcB (fun g => S.aB g i) (S.lift.1.1 i i)
  · exact hcB (S.ψB v i) (S.lift.1.2 v i)
  · obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz j N
    refine ⟨M, fun a ha hm => ?_⟩
    obtain ⟨b, hb, hb1, -⟩ := hT N j _ (hM ⟨(hgr j a).1 ha, hm⟩)
    have hba : b = a := Subtype.ext hb
    rw [← hba]
    exact hb1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrTbox
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_tbox :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ [IsCO O (ResidueField O)] [IsCO O (DualNumber (ResidueField O))] (B : Box F n (ResidueField O)), (IsLocallyConstant fun s => (B.r s).mat) → ∀ x ∈ Z1C F.loc B.ad B.b, ∃ B' : Box F n (DualNumber (ResidueField O)), B'.Cont (maximalIdeal _) ∧ B'.map (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O) : (DualNumber (ResidueField O)) →+* ResidueField O) = B ∧ ∀ s, (B'.r s).mat.map TrivSqZeroExt.snd = x.1 s * (B.r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ _ _ B hB x hx
  have hres : ∀ y : ResidueField O, res O (ResidueField O) y = y := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    have h := (res O (ResidueField O)).commutes a
    rw [IsLocalRing.ResidueField.algebraMap_eq] at h
    exact h
  have hbar : Box.bar O B = B := by
    apply Box.ext
    · ext s
      · simp [Box.bar, Box.map, GG.map, hres]
      · simp [Box.bar, Box.map, GG.map]
    · funext v
      ext i j
      simp [Box.bar, Box.map, hres]
  let ι : ResidueField O →+* DualNumber (ResidueField O) := algebraMap _ _
  let p := TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)
  have hp : ∀ X : GL (Fin n) (ResidueField O), GeneralLinearGroup.map (p : DualNumber (ResidueField O) →+* ResidueField O) (GeneralLinearGroup.map ι X) = X := by
    intro X
    ext i j
    simp [p, ι, TrivSqZeroExt.algebraMap_eq_inl]
  have hloc : ∀ v, Continuous (F.loc v) := by
    intro v
    exact continuous_subtype_val.comp (hF.loc_cont v)
  have hlc : ∀ (f : Matrix (Fin n) (Fin n) (ResidueField O) → DualNumber (ResidueField O)) (N : ℕ),
      IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal (DualNumber (ResidueField O)) ^ N) (f (B.r s).mat) :=
    fun f N => hB.comp (fun M => Ideal.Quotient.mk _ (f M))
  let D : SetLift p B :=
    { r := fun s => GeneralLinearGroup.map ι (B.r s).left
      r_cont := fun i j N => hlc (fun M => ι (M i j)) N
      r_map := fun s => hp _
      g := fun v => GeneralLinearGroup.map ι (B.g v)
      g_map := fun v => hp _
      t := fun v s => GeneralLinearGroup.map ι (B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹)
      t_cont := by
        intro v i j N
        have h := (hlc (fun M => ι (((B.g v).val * M * (B.g v)⁻¹.val) i j)) N).comp_continuous (hloc v)
        exact h
      t_tri := by
        intro v s i j hij
        have h := congrArg ι (B.tri v s i j hij)
        rw [map_zero] at h
        exact h
      t_map := fun v s => hp _ }
  let μ : ResidueField O →+ DualNumber (ResidueField O) :=
    (TrivSqZeroExt.inrHom (ResidueField O) (ResidueField O)).toAddMonoidHom
  have hresD : ∀ a : DualNumber (ResidueField O), res O (DualNumber (ResidueField O)) a = a.fst := by
    intro a
    rw [← res_map p a, hres]
    rfl
  have hμ : IsSq O μ := by
    constructor
    · intro a c
      rw [hresD]
      ext
      · simp [μ]
      · show (TrivSqZeroExt.inr (a.fst * c) : DualNumber (ResidueField O)).snd = (a * TrivSqZeroExt.inr c).snd
        rw [TrivSqZeroExt.snd_mul]
        simp only [TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, MulOpposite.op_zero, zero_smul, add_zero, smul_eq_mul]
    · intro c
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map p
      simp [p, μ] at this
  have hR : ∀ s t : F.Γ, GeneralLinearGroup.map ι (B.r (s * t)).left =
      GeneralLinearGroup.map ι (B.r s).left * sgnAct n _ (F.del s) (GeneralLinearGroup.map ι (B.r t).left) := by
    intro s t
    have h1 := congrArg SemidirectProduct.left (map_mul ((GG.map ι).comp B.r) s t)
    have h2 : (((GG.map ι).comp B.r) s).right = F.del s := B.nu s
    rw [SemidirectProduct.mul_left, h2] at h1
    exact h1
  refine (pr_correct hF O _ _ p B D μ hμ (fun c => by simp [p, μ]) (fun s => -x.1 s) (fun v => -x.2 v)
    (fun _ _ => 0) ?g1 ?g2 ?g3 ?g4).imp fun B' h => ⟨h.1, h.2.1, fun s => ?g5⟩
  case g5 =>
    rw [h.2.2 s]
    ext i j
    show (((1 - (-x.1 s).map μ) * ((B.r s).left.val.map ι) : Matrix (Fin n) (Fin n) (DualNumber (ResidueField O))) i j).snd = _
    rw [Matrix.mul_apply, TrivSqZeroExt.snd_sum, GG.mat, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [TrivSqZeroExt.snd_mul]
    simp [Matrix.one_apply, μ, ι, TrivSqZeroExt.algebraMap_eq_inl, op_smul_eq_mul]
    left
    split_ifs <;> simp
  case g1 => exact hx.1.comp (fun M => -M)
  case g2 =>
    intro y
    rw [hbar]
    have hc := hx.2.1 y.1 y.2
    have h0 : dOne B.ad (fun s => -x.1 s) y = 0 := by
      simp only [dOne, map_neg, hc]
      abel
    rw [h0, Matrix.map_zero _ (map_zero μ)]
    show (GeneralLinearGroup.map ι (B.r y.1).left * sgnAct n _ (F.del y.1) (GeneralLinearGroup.map ι (B.r y.2).left) *
      (GeneralLinearGroup.map ι (B.r (y.1 * y.2)).left)⁻¹).val - 1 = 0
    rw [hR, mul_inv_cancel, Units.val_one, sub_self]
  case g3 =>
    intro v s
    rw [Matrix.map_zero _ (map_zero μ)]
    show (GeneralLinearGroup.map ι (B.r (F.loc v s)).left * ((GeneralLinearGroup.map ι (B.g v))⁻¹ *
      GeneralLinearGroup.map ι (B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹) * GeneralLinearGroup.map ι (B.g v))⁻¹).val - 1 = 0
    simp [map_mul, map_inv, mul_assoc]
  case g4 =>
    intro v s
    rw [hbar]
    have h := hx.2.2 v s
    convert h using 1
    simp only [map_neg]
    abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ValSubOneMap
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] {C' : Type} [CommRing C'] [Algebra O C'] [IsCO O C']
  {C'' : Type} [CommRing C''] [Algebra O C''] [IsCO O C'']

private theorem mem_max_iff (q : C' →ₐ[O] C'') (x : C') : q x ∈ maximalIdeal C'' ↔ x ∈ maximalIdeal C' := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem adicCont_map {Γ : Type} [TopologicalSpace Γ] (q : C' →ₐ[O] C'') {f : Γ → C'}
    (hf : AdicCont (maximalIdeal C') f) : AdicCont (maximalIdeal C'') fun g => q (f g) := by
  intro N
  have hle : maximalIdeal C' ^ N ≤ (maximalIdeal C'' ^ N).comap (q : C' →+* C'') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    exact (mem_max_iff q y).2 hy
  exact (hf N).comp (Ideal.quotientMap _ (q : C' →+* C'') hle)

private theorem map_sgnAct {m : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (s : ℤˣ)
    (g : GL (Fin m) A) :
    GeneralLinearGroup.map f (sgnAct m A s g) = sgnAct m A' s (GeneralLinearGroup.map f g) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one, sgnAct_one]
  · rw [sgnAct_neg_one, sgnAct_neg_one, map_theta]

private theorem val_sub_one_map {m : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A')
    (g : GL (Fin m) A) (i j : Fin m) :
    (((GeneralLinearGroup.map f g : GL (Fin m) A') : Matrix (Fin m) (Fin m) A') - 1) i j =
      f (((g : Matrix (Fin m) (Fin m) A) - 1) i j) := by
  have e : ((GeneralLinearGroup.map f g : GL (Fin m) A') : Matrix (Fin m) (Fin m) A') - 1 =
      f.mapMatrix ((g : Matrix (Fin m) (Fin m) A) - 1) := by
    rw [map_sub, map_one]
    rfl
  rw [e]
  rfl

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
  {R : Type} [CommRing R] [Algebra O R] {B : Box F n R}

private noncomputable def push (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B) :
    SetLift p'' B where
  r s := GeneralLinearGroup.map (q : C' →+* C'') (D.r s)
  r_cont i j := adicCont_map q (D.r_cont i j)
  r_map s := D.r_map s
  g v := GeneralLinearGroup.map (q : C' →+* C'') (D.g v)
  g_map v := D.g_map v
  t v s := GeneralLinearGroup.map (q : C' →+* C'') (D.t v s)
  t_cont v i j := adicCont_map q (D.t_cont v i j)
  t_tri v s i j h := (congrArg q (D.t_tri v s i j h)).trans (map_zero q)
  t_map v s := D.t_map v s

private theorem push_om (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B)
    (x : F.Γ × F.Γ) (i j : Fin n) : (push q p'' D).om x i j = q (D.om x i j) := by
  refine Eq.trans ?_ (val_sub_one_map (q : C' →+* C'') _ i j)
  rw [map_mul, map_mul, map_inv, map_sgnAct]
  rfl

private theorem push_a (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R) (D : SetLift (p''.comp q) B)
    (v : F.V) (s : F.Gv v) (i j : Fin n) : (push q p'' D).a v s i j = q (D.a v s i j) := by
  refine Eq.trans ?_ (val_sub_one_map (q : C' →+* C'') _ i j)
  rw [map_mul, map_inv, map_mul, map_mul, map_inv]
  rfl

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.pr_obs :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → D.co u ∈ continuousCoboundaries2 F.loc (B.bar O).ad (B.bar O).b → ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R), p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u y = 0 → q y = 0) → ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ ρ B hU hOf hC hG C' _ _ _ p D u hsm hco C'' _ _ _ q p'' hpq hq hu
  subst hpq
  have hK : RingHom.ker (p''.comp q) ≤ maximalIdeal C' := fun y hy => by
    rw [← mem_max_iff (p''.comp q), (RingHom.mem_ker).1 hy]
    exact zero_mem _
  obtain ⟨μ, hμ, hμu, hμq⟩ := pr_mu O C' C'' _ q u hsm hK hq hu
  obtain ⟨hom, ha, -, -⟩ := pr_omk hF O C' R (p''.comp q) B D hsm
  obtain ⟨β, Y, hβ, h1, h2⟩ := hco
  have hev : ∀ y ∈ RingHom.ker (p''.comp q), q y = μ (evK _ u y) := fun y hy => by
    rw [evK_of_mem u hy, hμu]
  have hp0 : ∀ c, p'' (μ c) = 0 := fun c => by
    obtain ⟨y, hy⟩ := hμq c
    rw [hy]
    exact y.2
  obtain ⟨B', hB'c, hB'm, -⟩ := pr_correct hF O C'' R p'' B (push q p'' D) μ hμ hp0 β Y (D.co u).2 hβ
    (fun x => by
      rw [← h1]
      ext i j
      rw [push_om, hev _ (hom x i j)]
      rfl)
    (fun v s => by
      ext i j
      rw [push_a, hev _ (ha v s i j)]
      rfl) h2
  have hsm'' : maximalIdeal C'' * RingHom.ker p'' = ⊥ := by
    refine le_bot_iff.1 (Ideal.mul_le.2 fun a ha' b hb => ?_)
    obtain ⟨a, rfl⟩ := hq a
    obtain ⟨b, rfl⟩ := hq b
    have hab : a * b ∈ maximalIdeal C' * RingHom.ker (p''.comp q) :=
      Ideal.mul_mem_mul ((mem_max_iff q a).1 ha') hb
    rw [hsm, Ideal.mem_bot] at hab
    rw [← map_mul, hab, map_zero]
    exact zero_mem _
  obtain ⟨-, ρ', -, hρm, hρc, -, -⟩ := pr_norm hF O C'' R p'' ρ B' hsm'' hG (hB'm ▸ hOf) hB'c
  have hbar : ρ'.bar O = ρ.bar O := by
    have e : (res O C'' : C'' →+* ResidueField O) =
        (res O R : R →+* ResidueField O).comp (p'' : C'' →+* R) :=
      RingHom.ext fun x => (res_map p'' x).symm
    show ρ'.map _ = ρ.map _
    rw [e, ← NRep.map_map, hρm]
  obtain ⟨g, hg, -⟩ := hU.univ C'' ρ' hρc hbar
  obtain ⟨g', -, hg'⟩ := hU.univ R ρ hU.cont rfl
  refine ⟨g, (hg' _ ?_).trans (hg' _ rfl).symm⟩
  show ρ.map ((p'' : C'' →+* R).comp (g : R →+* C'')) = ρ
  rw [← NRep.map_map, hg, hρm]
end

