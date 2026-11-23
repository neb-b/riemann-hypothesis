module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumePiLatticeUnitaryCoordinates
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.CovPi

open GlobalTheory.HomCovolume

theorem hasCov_pi {β : Type} [Fintype β] {V : β → Type} [∀ b, NormedAddCommGroup (V b)]
    [∀ b, NormedSpace ℝ (V b)] [∀ b, FiniteDimensional ℝ (V b)] [∀ b, MeasurableSpace (V b)]
    [∀ b, BorelSpace (V b)] {μ : ∀ b, Measure (V b)} [∀ b, (μ b).IsAddHaarMeasure]
    {L : ∀ b, Submodule ℤ (V b)} {c : β → ℝ} (h : ∀ i, HasCov (μ i) (L i) (c i)) :
    HasCov (Measure.pi μ) (Submodule.pi Set.univ L) (∏ i, c i) := by
  classical
  have hd : ∀ i, DiscreteTopology (L i) := fun i => (h i).1
  have hz : ∀ i, IsZLattice ℝ (L i) := fun i => (h i).2.1
  have hc : ∀ i, ZLattice.covolume (L i) (μ i) = c i := fun i => (h i).2.2
  let B : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex ℤ (L i)) ℝ (V i) := fun i =>
    (Module.Free.chooseBasis ℤ (L i)).ofZLatticeBasis ℝ
  have hBmem : ∀ i j, B i j ∈ L i := fun i j => by
    simp only [B, Module.Basis.ofZLatticeBasis_apply]
    exact (Module.Free.chooseBasis ℤ (L i) j).2
  have hBspan : ∀ i, Submodule.span ℤ (Set.range (B i)) = L i := fun i =>
    (Module.Free.chooseBasis ℤ (L i)).ofZLatticeBasis_span ℝ
  have hspan : Submodule.pi Set.univ L = Submodule.span ℤ (Set.range (Pi.basis B)) := by
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_pi] at hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hxi : x i ∈ Submodule.span ℤ (Set.range (B i)) := by
        rw [hBspan]; exact hx i (Set.mem_univ i)
      refine Submodule.span_induction
        (p := fun y _ => Pi.single i y ∈ Submodule.span ℤ (Set.range (Pi.basis B))) ?_ ?_ ?_ ?_ hxi
      · rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span ⟨⟨i, j⟩, by simp⟩
      · simp
      · intro y z _ _ hy hz
        rw [Pi.single_add]; exact add_mem hy hz
      · intro a y _ hy
        rw [Pi.single_smul]; exact Submodule.smul_mem _ a hy
    · rw [Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_pi]
      intro i' _
      rw [Pi.basis_apply]
      by_cases hi : i' = i
      · subst hi; simpa using hBmem i' j
      · simp [hi]
  rw [hspan]
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (Pi.basis B) _)]
  have hfd : ZSpan.fundamentalDomain (Pi.basis B) = Set.univ.pi fun i => ZSpan.fundamentalDomain (B i) := by
    ext x
    simp [ZSpan.mem_fundamentalDomain, Pi.basis_repr, Sigma.forall]
  rw [hfd, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hc i, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (L i)) (μ i)), measureReal_def]

theorem measurePreserving_of_sum_sq {κ σ : Type} [Fintype κ] [Fintype σ]
    (e : (κ → ℂ) ≃L[ℝ] (σ → ℂ)) (he : ∀ z, ∑ j, ‖e z j‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) :
    MeasurePreserving e volume volume := by
  let T : EuclideanSpace ℂ κ ≃L[ℝ] (κ → ℂ) := ((EuclideanSpace.equiv κ ℂ).toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv
  have hnorm : ∀ v : EuclideanSpace ℂ κ, ‖v‖ ^ 2 = ∑ i, ‖T v i‖ ^ 2 := fun v => by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have hT : MeasurePreserving T volume volume :=
    GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords _ κ T hnorm
  have hTe : MeasurePreserving (T.trans e) volume volume :=
    GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords _ σ (T.trans e) fun v => by
      rw [hnorm v, ContinuousLinearEquiv.trans_apply, he]
  have hTs := MeasurePreserving.symm T.toHomeomorph.toMeasurableEquiv hT
  have hfun : (⇑e) = (T.trans e) ∘ T.toHomeomorph.toMeasurableEquiv.symm := by
    funext z
    simp
  rw [hfun]
  exact hTe.comp hTs

private theorem measurePreserving_piCurry_complex {I : Type} [Fintype I] {K : I → Type} [∀ i, Fintype (K i)] :
    MeasurePreserving (MeasurableEquiv.piCurry fun (i : I) (_ : K i) => ℂ) volume volume := by
  refine ⟨(MeasurableEquiv.piCurry _).measurable, ?_⟩
  symm
  show Measure.pi (fun i : I => Measure.pi fun _ : K i => (volume : Measure ℂ)) = _
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.pi Set.univ '' Set.pi Set.univ fun _ : K i => {s : Set ℂ | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun _ => (volume : Measure ℂ).toFiniteSpanningSetsIn) ?_
  intro s hs
  choose t ht hst using hs
  obtain rfl : s = fun i => Set.univ.pi (t i) := funext fun i => (hst i).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.piCurry fun (i : I) (_ : K i) => ℂ) ⁻¹'
      Set.univ.pi (fun i => Set.univ.pi (t i)) = Set.univ.pi fun p : (Σ i, K i) => t p.1 p.2 := by
    ext f
    simp [MeasurableEquiv.coe_piCurry, Sigma.forall]
    exact Iff.rfl
  rw [hpre, volume_pi, Measure.pi_pi, Fintype.prod_sigma]
  simp only [Measure.pi_pi]

attribute [local instance] haar_two haar_three

theorem covolume_pi_unitary : ∀ (ι κ β : Type) [Fintype ι] [Fintype κ] [Fintype β] (r s : β → ℕ) (Φ : ι → ((κ → ℂ) ≃ₗ[ℂ] (∀ b : β, Fin (r b) → Fin (s b) → ℂ))), (∀ v z, ∑ b, ∑ p, ∑ q, ‖Φ v z b p q‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) → ∀ (M : ∀ b : β, Submodule ℤ (ι → Fin (r b) → Fin (s b) → ℂ)), (∀ b, ∃ _ : DiscreteTopology (M b), IsZLattice ℝ (M b)) → ∀ L : Submodule ℤ (ι → κ → ℂ), (∀ z, z ∈ L ↔ ∀ b, (fun v => Φ v (z v) b) ∈ M b) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = ∏ b, ZLattice.covolume (M b) volume := by
  intro ι κ β _ _ _ r s Φ hΦ M hM L hL
  classical
  let Ψ : (ι → κ → ℂ) ≃ₗ[ℂ] (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ) :=
    { toFun := fun z b v => Φ v (z v) b
      invFun := fun w v => (Φ v).symm fun b => w b v
      map_add' := fun x y => by funext b v; simp
      map_smul' := fun c x => by funext b v; simp
      left_inv := fun z => by funext v; simp
      right_inv := fun w => by funext b v; simp }
  let F : ((Σ b : β, Σ _ : ι, Σ _ : Fin (r b), Fin (s b)) → ℂ) ≃ₗ[ℂ]
      (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ) :=
    { toFun := fun w b v p q => w ⟨b, v, p, q⟩
      invFun := fun u x => u x.1 x.2.1 x.2.2.1 x.2.2.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let G := LinearEquiv.piCurry ℂ fun (_ : ι) (_ : κ) => ℂ
  let E := G.trans (Ψ.trans F.symm)
  have hE : MeasurePreserving (E.restrictScalars ℝ).toContinuousLinearEquiv volume volume := by
    apply measurePreserving_of_sum_sq
    intro z
    have hz : ∀ j : (Σ b : β, Σ _ : ι, Σ _ : Fin (r b), Fin (s b)),
        (E.restrictScalars ℝ).toContinuousLinearEquiv z j =
          Φ j.2.1 (fun k => z ⟨j.2.1, k⟩) j.1 j.2.2.1 j.2.2.2 := fun j => rfl
    simp only [hz, Fintype.sum_sigma]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => hΦ v _
  have hG : MeasurePreserving (MeasurableEquiv.piCurry fun (_ : ι) (_ : κ) => ℂ) volume volume :=
    measurePreserving_piCurry_complex
  have hF : MeasurePreserving F volume volume := by
    have h := (volume_preserving_pi fun b => volume_preserving_pi fun (_ : ι) =>
        measurePreserving_piCurry_complex (I := Fin (r b)) (K := fun _ => Fin (s b))).comp
      ((volume_preserving_pi fun b =>
        measurePreserving_piCurry_complex (I := ι) (K := fun _ => Σ _ : Fin (r b), Fin (s b))).comp
        (measurePreserving_piCurry_complex (I := β) (K := fun b => Σ _ : ι, Σ _ : Fin (r b), Fin (s b))))
    exact h
  have hΨ : MeasurePreserving (Ψ.restrictScalars ℝ).toContinuousLinearEquiv volume volume := by
    have h := hF.comp (hE.comp (MeasurePreserving.symm _ hG))
    convert h using 1
    funext z
    rfl
  have := haar_two ι κ
  have hB3 : ∀ b, (volume : Measure (ι → Fin (r b) → Fin (s b) → ℂ)).IsAddHaarMeasure :=
    fun b => haar_three ι _ _
  have : (volume : Measure (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ)).IsAddHaarMeasure := by
    rw [← hΨ.map_eq]; infer_instance
  show HasCov volume L _
  refine HasCov.of_measurePreserving (Ψ.restrictScalars ℝ).toContinuousLinearEquiv hΨ
    (L' := Submodule.pi Set.univ M) ?_ ?_
  · intro z
    rw [hL, Submodule.mem_pi]
    simp only [Set.mem_univ, true_implies]
    exact Iff.rfl
  · exact hasCov_pi (μ := fun _ => volume) fun b => by
      obtain ⟨hd, hz⟩ := hM b
      exact ⟨hd, hz, rfl⟩

end GlobalTheory.CovPi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe
section
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.FrEqv

section Count

variable {α : Type} {R : α → α → Prop}

theorem cntCl_eq_encard (hR : Equivalence R) (X : Set α) :
    cntCl X R = ((fun a => {b | R a b}) '' X).encard := by

  have hset : {O : Set α | ∃ a ∈ X, O = {b | b ∈ X ∧ R a b}} =
      (fun O => {b | b ∈ O ∧ b ∈ X}) '' ((fun a => {b | R a b}) '' X) := by
    ext O
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨{b | R a b}, ⟨a, ha, rfl⟩, by ext b; simp [and_comm]⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, by ext b; simp [and_comm]⟩
  rw [cntCl, hset]
  apply Set.InjOn.encard_image
  rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ hEq
  have hEq' : {b | b ∈ {b | R a b} ∧ b ∈ X} = {b | b ∈ {b | R a' b} ∧ b ∈ X} := hEq
  have hmem : a' ∈ {b | b ∈ {b | R a b} ∧ b ∈ X} := by
    rw [hEq']
    exact ⟨hR.refl a', ha'⟩
  have haa' : R a a' := hmem.1
  ext b
  exact ⟨fun hb => hR.trans (hR.symm haa') hb, fun hb => hR.trans haa' hb⟩

theorem encard_biUnion_le' {ι β : Type} (s : Finset ι) (Y : ι → Set β) :
    (⋃ i ∈ s, Y i).encard ≤ ∑ i ∈ s, (Y i).encard := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (add_le_add le_rfl ih)

theorem cntCl_le_sum (hR : Equivalence R) {ι : Type} (s : Finset ι) (X : Set α) (Y : ι → Set α)
    (h : ∀ a ∈ X, ∃ i ∈ s, ∃ b ∈ Y i, R a b) : cntCl X R ≤ ∑ i ∈ s, cntCl (Y i) R := by
  simp only [cntCl_eq_encard hR]
  calc ((fun a => {b | R a b}) '' X).encard
      ≤ (⋃ i ∈ s, (fun a => {b | R a b}) '' Y i).encard := by
        apply Set.encard_le_encard
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨i, hi, b, hb, hab⟩ := h a ha
        refine Set.mem_biUnion hi ⟨b, hb, ?_⟩
        ext c
        exact ⟨fun hc => hR.trans hab hc, fun hc => hR.trans (hR.symm hab) hc⟩
    _ ≤ ∑ i ∈ s, ((fun a => {b | R a b}) '' Y i).encard := encard_biUnion_le' s _

end Count

section Grp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
  {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T}

theorem mem_gmap (g : S.V ≃ₗ[E] S.V) (x : S.V) : x ∈ Formalism.HermitianLatticesTheory.gmap g Λ ↔ g.symm x ∈ Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨g.symm x, hx, by simp⟩

theorem aut_mem_iff {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) (x : S.V) : n x ∈ Λ ↔ x ∈ Λ := by
  have hx := mem_gmap (Λ := Λ) n (n x)
  rw [hn.2, LinearEquiv.symm_apply_apply] at hx
  exact hx

theorem Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  show Submodule.span E (F.fl.e '' {i | i.1 < j}) ≤ Submodule.span E (F.fl.e '' {i | i.1 < j + 1})
  exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => Nat.lt_succ_of_lt hi)

theorem X_le_orth : Xsp F ≤ orth S (Xsp F) := by

  have key : ∀ a, Xsp F ≤ LinearMap.ker (S.hT (F.fl.e a)) := fun a => by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact F.fl.e_iso a b
  intro y hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  have key2 : Xsp F ≤ LinearMap.ker (S.hT.flip y) := by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact key a hy
  simpa using key2 hx

theorem symm_sub_mem (n : S.V ≃ₗ[E] S.V) {A B : Submodule E S.V} (hAB : A ≤ B)
    (h : ∀ x ∈ B, n x - x ∈ A) : ∀ x ∈ B, n.symm x - x ∈ A := by
  intro x hx

  have hmap : ∀ y ∈ B, n y ∈ B := fun y hy => by simpa using B.add_mem (hAB (h y hy)) hy
  have hinj : Function.Injective (n.toLinearMap.restrict hmap) := fun a b hab =>
    Subtype.ext (n.injective (congrArg Subtype.val hab))
  obtain ⟨⟨y, hy⟩, hyx⟩ := LinearMap.surjective_of_injective hinj ⟨x, hx⟩
  have hny : n y = x := congrArg Subtype.val hyx
  have hy' : n.symm x = y := by rw [← hny, LinearEquiv.symm_apply_apply]
  rw [hy', ← neg_sub]
  have hxy := h y hy
  rw [hny] at hxy
  exact A.neg_mem hxy

theorem trans_sub_mem (n m : S.V ≃ₗ[E] S.V) {A B : Submodule E S.V} (hAB : A ≤ B)
    (h : ∀ x ∈ B, n x - x ∈ A) (h' : ∀ x ∈ B, m x - x ∈ A) : ∀ x ∈ B, (m * n) x - x ∈ A := by
  intro x hx
  have hnx : n x ∈ B := by simpa using B.add_mem (hAB (h x hx)) hx
  show m (n x) - x ∈ A
  have e : m (n x) - x = (m (n x) - n x) + (n x - x) := by abel
  rw [e]
  exact A.add_mem (h' _ hnx) (h x hx)

theorem one_mem_NLam : (1 : S.V ≃ₗ[E] S.V) ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).one_mem, ?_⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · ext x
    rw [mem_gmap]
    rfl
  · simp
  · simp

theorem mul_mem_NLam {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F) : m * n ∈ NLam Λ F := by
  have hsymm : ∀ {k : S.V ≃ₗ[E] S.V}, IsAutLam S Λ k → ∀ y, k.symm y ∈ Λ ↔ y ∈ Λ := fun hk y => by
    rw [← aut_mem_iff hk, LinearEquiv.apply_symm_apply]
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).mul_mem hm.1.1 hn.1.1, ?_⟩,
    fun j => trans_sub_mem n m (Xflag_mono j) (hn.2.1 j) (hm.2.1 j),
    trans_sub_mem n m X_le_orth hn.2.2 hm.2.2⟩
  ext x
  rw [mem_gmap]
  exact (hsymm hn.1 _).trans (hsymm hm.1 _)

theorem symm_mem_NLam {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : n.symm ∈ NLam Λ F := by
  refine ⟨⟨(Formalism.HermitianLatticesTheory.isom S.hT).inv_mem hn.1.1, ?_⟩,
    fun j => symm_sub_mem n (Xflag_mono j) (hn.2.1 j), symm_sub_mem n X_le_orth hn.2.2⟩
  ext x
  rw [mem_gmap, LinearEquiv.symm_symm]
  exact aut_mem_iff hn.1 x

theorem frameAct_one {k : ℕ} (f : Fin k → S.V) : frameAct f 1 = f := by
  funext b
  simp only [frameAct]
  rw [Finset.sum_eq_single b (fun a _ hab => by rw [Matrix.one_apply_ne hab]; simp)
    (fun hb => absurd (Finset.mem_univ b) hb), Matrix.one_apply_eq]
  simp

theorem frameAct_mul {k : ℕ} (f : Fin k → S.V) (ξ η : Matrix (Fin k) (Fin k) (𝓞 E)) :
    frameAct (frameAct f ξ) η = frameAct f (ξ * η) := by
  funext b
  simp only [frameAct, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem map_frameAct {k : ℕ} (n : S.V ≃ₗ[E] S.V) (f : Fin k → S.V) (ξ : Matrix (Fin k) (Fin k) (𝓞 E)) :
    (fun a => n (frameAct f ξ a)) = frameAct (fun a => n (f a)) ξ := by
  funext b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [frameAct, map_sum, map_smul]

theorem uni_mul {k : ℕ} {O : Type} [CommRing O] {ξ η : Matrix (Fin k) (Fin k) O}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a b, b < a → η a b = 0) (a : Fin k) :
    (ξ * η) a a = ξ a a * η a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with hc | hc
    · rw [h1 a c hc, zero_mul]
    · rw [h2 c a hc, mul_zero]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

theorem uni_inv {k : ℕ} {O : Type} [CommRing O] {ξ : Matrix (Fin k) (Fin k) O}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    ∃ η : Matrix (Fin k) (Fin k) O, (∀ a b, b < a → η a b = 0) ∧ (∀ a, η a a = 1) ∧ ξ * η = 1 := by

  have hbt : ξ.BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : ξ.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]
    simp [h2]
  have hu : IsUnit ξ.det := by
    rw [hdet]
    exact isUnit_one
  let _ := Matrix.invertibleOfIsUnitDet ξ hu
  have hinv : ξ⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have hmul : ξ * ξ⁻¹ = 1 := Matrix.mul_nonsing_inv ξ hu
  refine ⟨ξ⁻¹, fun a b hab => hinv hab, fun a => ?_, hmul⟩
  have hd := uni_mul h1 (fun a b hab => hinv hab) a
  rw [hmul, Matrix.one_apply_eq, h2, one_mul] at hd
  exact hd.symm

end Grp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem TEqv_equivalence (D : D7) (Λ : LatV D) {T T' : D.host.E} (F : Fg D T) :
    Equivalence (TEqv D Λ F (T' := T')) := by
  refine ⟨fun F' => ?_, fun {F₁ F₂} h => ?_, fun {F₁ F₂ F₃} h h' => ?_⟩
  · refine ⟨1, one_mem_NLam, 1, fun a b hab => Matrix.one_apply_ne (ne_of_gt hab), fun a => Matrix.one_apply_eq a, ?_⟩
    rw [frameAct_one]
    rfl
  · obtain ⟨n, hn, ξ, h1, h2, hfr⟩ := h
    obtain ⟨η, hη1, hη2, hξη⟩ := uni_inv h1 h2
    refine ⟨n.symm, symm_mem_NLam hn, η, hη1, hη2, ?_⟩
    rw [hfr, map_frameAct]
    simp only [LinearEquiv.symm_apply_apply]
    rw [frameAct_mul, hξη, frameAct_one]
  · obtain ⟨n, hn, ξ, h1, h2, hfr⟩ := h
    obtain ⟨m, hm, ζ, k1, k2, hfr'⟩ := h'
    refine ⟨m * n, mul_mem_NLam hn hm, ξ * ζ, fun a b hab => ?_, fun a => ?_, ?_⟩
    · exact Matrix.BlockTriangular.mul (b := id) (fun i j hij => h1 i j hij) (fun i j hij => k1 i j hij) hab
    · rw [uni_mul h1 k1 a, h2, k2, one_mul]
    · rw [hfr', hfr, map_frameAct, frameAct_mul]
      rfl

end GlobalTheory.LoopC.FrEqv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualOfAnisotropicOrthogonal
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem exists_dual_of_anisotropic_orthogonal (E : Type) [Field E] [StarRing E] (n m : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin m) (Fin m) E) (x : Fin n → E)
    (A : Matrix (Fin n) (Fin m) E) (hn : m + 1 = n) (hJ : Jᴴ = J) (hdet : J'.det ≠ 0)
    (hβ : star x ⬝ᵥ (J *ᵥ x) ≠ 0) (hx : star x ᵥ* (J * A) = 0) (hA : Aᴴ * J * A = J') :
    ∃ (u : Fin n → E) (A' : Matrix (Fin m) (Fin n) E), A' * A = 1 ∧ A' *ᵥ x = 0 ∧
      u ᵥ* A = 0 ∧ u ⬝ᵥ x = 1 ∧ vecMulVec x u + A * A' = 1 ∧ Aᴴ *ᵥ (J *ᵥ x) = 0 := by
  have h6 : Aᴴ *ᵥ (J *ᵥ x) = 0 := by
    have := congrArg star hx
    rw [Matrix.star_vecMul, star_star, Matrix.conjTranspose_mul, hJ, star_zero,
      ← Matrix.mulVec_mulVec] at this
    exact this
  obtain ⟨u, hu⟩ : ∃ u : Fin n → E, u = (star x ⬝ᵥ (J *ᵥ x))⁻¹ • (star x ᵥ* J) := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A' : Matrix (Fin m) (Fin n) E, A' = J'⁻¹ * Aᴴ * J := ⟨_, rfl⟩
  have h1 : A' * A = 1 := by
    rw [hA', Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA]
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hdet)
  have h2 : A' *ᵥ x = 0 := by
    rw [hA', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h6, Matrix.mulVec_zero]
  have h3 : u ᵥ* A = 0 := by
    rw [hu, Matrix.smul_vecMul, Matrix.vecMul_vecMul, hx, smul_zero]
  have h4 : u ⬝ᵥ x = 1 := by
    rw [hu, smul_dotProduct, ← Matrix.dotProduct_mulVec, smul_eq_mul, inv_mul_cancel₀ hβ]
  refine ⟨u, A', h1, h2, h3, h4, ?_, h6⟩
  subst hn
  let C : Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
    Matrix.of fun i j => (Fin.cons (x i) (fun k => A i k) : Fin (m + 1) → E) j
  let C' : Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
    Matrix.of fun i j => (Fin.cons (u j) (fun k => A' k j) : Fin (m + 1) → E) i
  have hCC : C' * C = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa [C, C', Matrix.mul_apply, dotProduct] using h4
    · have := congrFun h3 j
      simpa [C, C', Matrix.mul_apply, dotProduct, Matrix.vecMul, (Fin.succ_ne_zero j).symm] using this
    · have := congrFun h2 i
      simpa [C, C', Matrix.mul_apply, dotProduct, Matrix.mulVec, Fin.succ_ne_zero i] using this
    · have := congrFun (congrFun h1 i) j
      simpa [C, C', Matrix.mul_apply, Matrix.one_apply] using this
  have hCC' : C * C' = 1 := mul_eq_one_comm.mp hCC
  rw [← hCC']
  ext i j
  simp [C, C', Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMulVec_apply]

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorGramMatrixConstDoubleCoset
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem leadMinorE_zhatL_dcrel :
    ∀ (D : D7) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (T T' : D.host.E)
      (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T'),
      Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂ → ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l := by
  intro D Λ T T' F F₁ F₂ h l
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hZ⟩ := Formalism.L2.SG.Pf.zhat_rel F h
  rw [hZ]
  exact Formalism.L2.SG.Pf.leadMinor_uni A _ B hA0 hA1 hB0 hB1 l

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingTriangularShearStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_add_of_triangular : ∀ (d : ℕ) (deg : Fin d → ℕ) (f : (Fin d → ℝ) → (Fin d → ℝ)), Measurable f → (∀ x y i, (∀ k, deg k < deg i → x k = y k) → f x i = f y i) → MeasurePreserving (fun x => x + f x) (volume : Measure (Fin d → ℝ)) volume := by
  first | exact @GlobalTheory.measurePreserving_triangular_shear | exact GlobalTheory.measurePreserving_triangular_shear | (intros; apply GlobalTheory.measurePreserving_triangular_shear <;> assumption)
end

