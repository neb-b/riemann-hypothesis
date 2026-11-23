module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PiIsot
section
open UpperTheory.V.Z.J.D
open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

section Ins

variable {I : Type} [DecidableEq I]

private def ins {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1) : ∀ i, β i :=
  fun i => if h : i = i₀ then h ▸ a else b ⟨i, h⟩

private lemma ins_self {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1) :
    ins i₀ a b i₀ = a := by
  simp [ins]

private lemma ins_ne {β : I → Type} (i₀ : I) (a : β i₀) (b : ∀ j : {i // i ≠ i₀}, β j.1)
    (j : {i // i ≠ i₀}) : ins i₀ a b j.1 = b j := by
  simp [ins, j.2]

private lemma ins_res {β : I → Type} (i₀ : I) (g : ∀ i, β i) :
    ins i₀ (g i₀) (fun j => g j.1) = g := by
  funext i
  by_cases h : i = i₀
  · subst h; exact ins_self _ _ _
  · exact ins_ne i₀ _ _ ⟨i, h⟩

private def insHom (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) :
    (Gi i₀ × ∀ j : {i // i ≠ i₀}, Gi j.1) →* ∀ i, Gi i where
  toFun p := ins i₀ p.1 p.2
  map_one' := by
    funext i
    by_cases h : i = i₀
    · subst h; exact ins_self _ _ _
    · exact ins_ne i₀ _ _ ⟨i, h⟩
  map_mul' p q := by
    funext i
    by_cases h : i = i₀
    · subst h
      simp only [Pi.mul_apply, ins_self, Prod.fst_mul]
    · have := fun (r : Gi i₀ × ∀ j : {i // i ≠ i₀}, Gi j.1) => ins_ne i₀ r.1 r.2 ⟨i, h⟩
      simp only [Pi.mul_apply] at this ⊢
      rw [this, this, this]
      rfl

private lemma insHom_res (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) (g : ∀ i, Gi i) :
    insHom Gi i₀ (g i₀, fun j => g j.1) = g :=
  ins_res i₀ g

private lemma insHom_inl (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) :
    (insHom Gi i₀).comp (MonoidHom.inl _ _) = MonoidHom.mulSingle Gi i₀ := by
  ext a i
  by_cases h : i = i₀
  · subst h
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
    exact ins_self _ _ _
  · simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h]
    exact ins_ne i₀ _ _ ⟨i, h⟩

private lemma insHom_inr (Gi : I → Type) [∀ i, Group (Gi i)] (i₀ : I) (j : {i // i ≠ i₀}) :
    ((insHom Gi i₀).comp (MonoidHom.inr _ _)).comp (MonoidHom.mulSingle (fun j : {i // i ≠ i₀} => Gi j.1) j) =
      MonoidHom.mulSingle Gi j.1 := by
  ext a i
  by_cases h : i = i₀
  · subst h
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.mulSingle_apply,
      Pi.mulSingle_eq_of_ne (Ne.symm j.2)]
    exact ins_self _ _ _
  · simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.mulSingle_apply]
    refine (ins_ne i₀ _ _ ⟨i, h⟩).trans ?_
    by_cases hj : i = j.1
    · subst hj
      simp
    · rw [Pi.mulSingle_eq_of_ne hj]
      have e : (⟨i, h⟩ : {i // i ≠ i₀}) ≠ j := fun e => hj (congrArg Subtype.val e)
      change (Pi.mulSingle j a : ∀ j : {i // i ≠ i₀}, Gi j.1) ⟨i, h⟩ = 1
      rw [Pi.mulSingle_eq_of_ne e]

private lemma res_update {β : I → Type} (i₀ i : I) (h : i ≠ i₀) (m : ∀ i, β i) (x : β i)
    [DecidableEq {i // i ≠ i₀}] [DecidableEq I] :
    (fun j : {i // i ≠ i₀} => Function.update m i x j.1) =
      Function.update (fun j : {i // i ≠ i₀} => m j.1) ⟨i, h⟩ x := by
  funext j
  by_cases hj : j = ⟨i, h⟩
  · subst hj; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne (fun e => hj (Subtype.ext e))]

private lemma res_update_self {β : I → Type} (i₀ : I) (m : ∀ i, β i) (x : β i₀) [DecidableEq I] :
    (fun j : {i // i ≠ i₀} => Function.update m i₀ x j.1) = fun j : {i // i ≠ i₀} => m j.1 :=
  funext fun j : {i // i ≠ i₀} => Function.update_of_ne j.2 _ _

private def split (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I) :
    (⨂[ℂ] i, Wi i) →ₗ[ℂ] Wi i₀ ⊗[ℂ] (⨂[ℂ] j : {i // i ≠ i₀}, Wi j.1) :=
  PiTensorProduct.lift
    { toFun := fun m => m i₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun j : {i // i ≠ i₀} => m j.1)
      map_update_add' := by
        intro _ m i x y
        by_cases h : i = i₀
        · subst h
          simp only [Function.update_self, res_update_self, TensorProduct.add_tmul]
        · classical
          simp only [Function.update_of_ne (Ne.symm h), res_update i₀ i h,
            MultilinearMap.map_update_add, TensorProduct.tmul_add]
      map_update_smul' := by
        intro _ m i c x
        by_cases h : i = i₀
        · subst h
          simp only [Function.update_self, res_update_self, TensorProduct.smul_tmul', RingHom.id_apply]
        · classical
          simp only [Function.update_of_ne (Ne.symm h), res_update i₀ i h,
            MultilinearMap.map_update_smul, TensorProduct.tmul_smul] }

private lemma split_tprod (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I)
    (m : ∀ i, Wi i) :
    split Wi i₀ (PiTensorProduct.tprod ℂ m) =
      m i₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun j : {i // i ≠ i₀} => m j.1) := by
  simp [split]

private lemma split_range (Wi : I → Type) [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (i₀ : I) :
    LinearMap.range (split Wi i₀) = ⊤ := by
  refine LinearMap.range_eq_top.2 fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ _ _⟩
  | tmul w t =>
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      refine ⟨r • PiTensorProduct.tprod ℂ (ins i₀ w m), ?_⟩
      rw [map_smul, split_tprod, ins_self, TensorProduct.tmul_smul]
      congr 3
      funext j
      exact ins_ne i₀ _ _ j
    | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x + y, by rw [map_add (f := _), hx, hy, TensorProduct.tmul_add]⟩

private lemma piRep_tprod {Gi Wi : I → Type} [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)]
    [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (g : ∀ i, Gi i) (m : ∀ i, Wi i) :
    piRep τ g (PiTensorProduct.tprod ℂ m) = PiTensorProduct.tprod ℂ fun i => τ i (g i) (m i) := by
  simp only [piRep, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
  rfl

private lemma split_intw [Fintype I] {Gi Wi : I → Type} [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)]
    [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) (i₀ : I) (g : ∀ i, Gi i)
    (t : ⨂[ℂ] i, Wi i) :
    split Wi i₀ (piRep τ g t) =
      box (τ i₀) (piRep fun j : {i // i ≠ i₀} => τ j.1) (g i₀, fun j => g j.1) (split Wi i₀ t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, map_smul, piRep_tprod, split_tprod, split_tprod]
    simp only [box, Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.comp_apply,
      MonoidHom.coe_fst, MonoidHom.coe_snd, piRep_tprod]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end Ins

private lemma piIsot_empty {I : Type} [Fintype I] [DecidableEq I] [IsEmpty I] (Gi Wi : I → Type)
    [∀ i, Group (Gi i)] [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)]
    (τ : ∀ i, Representation ℂ (Gi i) (Wi i)) {X : Type} [AddCommGroup X] [Module ℂ X]
    (κ : Representation ℂ (∀ i, Gi i) X) : Isot κ (piRep τ) := by
  intro x _
  let f : (⨂[ℂ] i, Wi i) →ₗ[ℂ] X :=
    (LinearMap.toSpanSingleton ℂ X x).comp (PiTensorProduct.isEmptyEquiv I).toLinearMap
  have hf : Intw (piRep τ) κ f := by
    intro g v
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp
  refine Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨PiTensorProduct.tprod ℂ isEmptyElim, ?_⟩
  simp [f, PiTensorProduct.isEmptyEquiv_apply_tprod]

private lemma piIsot_card (hB : BoxIsot) (hP : PiIrr) (n : ℕ) :
    ∀ (I : Type) [Fintype I] [DecidableEq I], Fintype.card I = n → ∀ (Gi Wi : I → Type) [∀ i, Group (Gi i)]
      [∀ i, AddCommGroup (Wi i)] [∀ i, Module ℂ (Wi i)] (τ : ∀ i, Representation ℂ (Gi i) (Wi i)),
      (∀ i, AbsIrr (τ i)) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X]
      (κ : Representation ℂ (∀ i, Gi i) X), (∀ i, Isot (κ.comp (MonoidHom.mulSingle Gi i)) (τ i)) →
      Isot κ (piRep τ) := by
  induction n with
  | zero =>
    intro I _ _ hc Gi Wi _ _ _ τ _ X _ _ κ _
    haveI : IsEmpty I := Fintype.card_eq_zero_iff.1 hc
    exact piIsot_empty Gi Wi τ κ
  | succ n ih =>
    intro I _ _ hc Gi Wi _ _ _ τ hτ X _ _ κ hκ
    haveI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨i₀⟩ := ‹Nonempty I›
    have hJ : Fintype.card {i // i ≠ i₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let J := {i // i ≠ i₀}
    let κ' : Representation ℂ (Gi i₀ × ∀ j : J, Gi j.1) X := κ.comp (insHom Gi i₀)
    have h1 : Isot (κ'.comp (MonoidHom.inl _ _)) (τ i₀) := by
      have : κ'.comp (MonoidHom.inl _ _) = κ.comp (MonoidHom.mulSingle Gi i₀) := by
        rw [← insHom_inl]; rfl
      rw [this]
      exact hκ i₀
    have h2 : Isot (κ'.comp (MonoidHom.inr _ _)) (piRep fun j : J => τ j.1) := by
      refine ih J hJ (fun j => Gi j.1) (fun j => Wi j.1) (fun j => τ j.1) (fun j => hτ j.1) X
        (κ'.comp (MonoidHom.inr _ _)) fun j => ?_
      have : (κ'.comp (MonoidHom.inr _ _)).comp (MonoidHom.mulSingle (fun j : J => Gi j.1) j) =
          κ.comp (MonoidHom.mulSingle Gi j.1) := by
        rw [← insHom_inr]; rfl
      rw [this]
      exact hκ j.1
    have h3 := hB _ _ _ _ (τ i₀) (piRep fun j : J => τ j.1) (hτ i₀)
      (hP J (fun j => Gi j.1) (fun j => Wi j.1) (fun j => τ j.1) fun j => hτ j.1) X κ' h1 h2
    refine le_trans h3 (iSup_le fun f => ?_)
    have hf : Intw (piRep τ) κ (f.1.comp (split Wi i₀)) := by
      intro g t
      have := f.2 (g i₀, fun j => g j.1) (split Wi i₀ t)
      simp only [LinearMap.comp_apply]
      rw [split_intw, this]
      change κ (insHom Gi i₀ _) _ = _
      rw [insHom_res]
    refine le_iSup_of_le ⟨_, hf⟩ ?_
    rw [LinearMap.range_comp_of_range_eq_top _ (split_range Wi i₀)]

theorem piIsot :
    BoxIsot → PiIrr → PiIsot := by
  intro hB hP I _ _ Gi Wi _ _ _ τ hτ X _ _ κ hκ
  exact piIsot_card hB hP _ I rfl Gi Wi τ hτ X κ hκ

end UpperTheory.V.Z.J.D
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PrimeNotMemSectionBasePlaceBis
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.J.D

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D.AuxBlock5

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}

private theorem cmp_of {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem cmp_over_l {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (x : Ga l L n) : cmp n w x = 1 := by
  unfold CaseU.cmp
  rw [dite_eq_right (not_not.2 h)]
  rfl

private theorem ext_cmp {x y : Ga l L n} (h : ∀ w, cmp n w x = cmp n w y) : x = y := by
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  obtain ⟨y, rfl⟩ := (away l L n).rangeRestrict_surjective y
  refine Subtype.ext (funext fun w => ?_)
  have e := h w.1
  rwa [cmp_of w.2, cmp_of w.2] at e

private theorem comm_of {a b : Ga l L n} (h : ∀ w, cmp n w a = 1 ∨ cmp n w b = 1) : Commute a b := by
  refine ext_cmp fun w => ?_
  rw [map_mul, map_mul]
  rcases h w with h | h <;> rw [h] <;> simp

private theorem l_under {u : Plc L} :
    ((l : ℕ) : 𝓞 L) ∈ u.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.under (𝓞 (Lp L))).asIdeal := by
  change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ u.asIdeal
  rw [map_natCast]

private theorem cLoc_over {w u : Plc L} (hw : IsSplitAt w) (x : UA L n) (h1 : cLoc w x = 1)
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) : cLoc u x = 1 := by
  have hw1 : ∀ v, v = w → cLoc v x = 1 := by
    rintro v rfl
    exact h1
  rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu with rfl | rfl
  · exact h1
  · have hce := GlobalTheory.SplitPts.comp_eq x (conjSrc (GlobalTheory.SplitPts.conjE L) w)
    rw [hw1 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.one_mul] at hce
    exact Units.ext hce

private theorem cmp_over {w u : Plc L} (hw : IsSplitAt w) (x : Ga l L n) (h1 : cmp n w x = 1)
    (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) : cmp n u x = 1 := by
  by_cases hl : ((l : ℕ) : 𝓞 L) ∈ u.asIdeal
  · exact cmp_over_l hl x
  have hl' : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun h => hl (l_under.2 (hu ▸ l_under.1 h))
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  rw [cmp_of hl'] at h1
  rw [cmp_of hl]
  exact cLoc_over hw x h1 hu

private theorem loc_one {w u : Plc L} {x : UA L n} (hx : x ∈ locU n w)
    (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) : cLoc u x = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)

variable (s : HidaSetting l L Ω)

private theorem under_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem split_of {v : Plc (Lp L)} (h : v ∈ s.St ∨ v = s.v0) : IsSplitAt (s.w v) :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v) (s.split v (Or.inr h)) _ (under_w s v)

private theorem SectionSplitPlaces : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := by
  intro h
  have hp := s.p_prime
  have hcard : Nat.card (𝓞 (Lp L) ⧸ s.v0.asIdeal) = s.p := s.norm_v0_eq_one
  have hl0 : ((l : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    exact (Ideal.Quotient.eq_zero_iff_mem.2 h : _) |> fun e => by simpa using e
  have hp0 : ((s.p : ℕ) : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    have := card_nsmul_eq_zero' (G := 𝓞 (Lp L) ⧸ s.v0.asIdeal) (x := 1)
    rw [hcard] at this
    simpa using this
  have hco : Nat.Coprime l s.p := (Nat.coprime_primes (Fact.out : l.Prime) hp).2 (Ne.symm s.p_ne)
  have h1 : (1 : 𝓞 (Lp L) ⧸ s.v0.asIdeal) = 0 := by
    have := Nat.Coprime.isCoprime hco
    obtain ⟨a, b, e⟩ := this
    have e' := congrArg (Int.cast : ℤ → 𝓞 (Lp L) ⧸ s.v0.asIdeal) e
    push_cast at e'
    rw [hl0, hp0] at e'
    simpa using e'.symm
  have hsub : Subsingleton (𝓞 (Lp L) ⧸ s.v0.asIdeal) := subsingleton_of_zero_eq_one h1.symm
  rw [Nat.card_of_subsingleton (0 : 𝓞 (Lp L) ⧸ s.v0.asIdeal)] at hcard
  exact hp.one_lt.ne hcard

private theorem away_of {v : Plc (Lp L)} (h : v ∈ s.St ∨ v = s.v0) : ((l : ℕ) : 𝓞 L) ∉ (s.w v).asIdeal := by
  intro e
  have e' := l_under.1 e
  rw [under_w] at e'
  rcases h with h | rfl
  · exact s.St_l _ h e'
  · exact SectionSplitPlaces s e'

private theorem mem_GaS {x : Ga l L n} : x ∈ GaS n s ↔
    ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0 → cmp n w x = 1 := by
  simp only [GaS, Subgroup.mem_iInf, MonoidHom.mem_ker]

private theorem toGS_one {x : Ga l L n} (h : toGS n s x = 1) {w : Plc L}
    (hw : w.under (𝓞 (Lp L)) ∈ s.St ∨ w.under (𝓞 (Lp L)) = s.v0) : cmp n w x = 1 := by
  rcases hw with hw | hw
  · have e : cmp n (s.w (w.under (𝓞 (Lp L)))) x = 1 := congrFun (congrArg Prod.fst h) ⟨_, hw⟩
    exact cmp_over (split_of s (Or.inl hw)) x e (under_w s _).symm
  · have e : cmp n (s.w s.v0) x = 1 := congrArg Prod.snd h
    exact cmp_over (split_of s (Or.inr rfl)) x e (by rw [under_w, hw])

private theorem build (hn : 1 ≤ n) (T : Finset (Plc (Lp L))) (hT : ∀ v ∈ T, IsSplitAt (s.w v))
    (f : ∀ v, GLw n (s.w v)) :
    ∃ x : UA L n, (∀ v ∈ T, cLoc (s.w v) x = f v) ∧ ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ T → cLoc w x = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun w _ => map_one _⟩
  | insert a T ha ih =>
    obtain ⟨x, hx, hx'⟩ := ih fun v hv => hT v (Finset.mem_insert_of_mem hv)
    obtain ⟨⟨j, hj, hj', -, -⟩, -⟩ := secU l L Ω s n hn (s.w a) (hT a (Finset.mem_insert_self _ _))
    have hloc : ∀ g (u : Plc L), u.under (𝓞 (Lp L)) ≠ a → cLoc u (j g) = 1 := fun g u hu =>
      loc_one (hj g) (by rwa [under_w])
    refine ⟨x * j (f a), fun v hv => ?_, fun w hw => ?_⟩
    · rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [map_mul, hj', hx' _ (by rwa [under_w]), one_mul]
      · rw [map_mul, hx v hv, hloc _ _ (by rw [under_w]; exact fun e => ha (e ▸ hv)), mul_one]
    · rw [map_mul, hx' w fun h => hw (Finset.mem_insert_of_mem h),
        hloc _ w fun h => hw (h ▸ Finset.mem_insert_self _ _), one_mul]

private theorem bij (hn : 1 ≤ n) : Function.Bijective ((toGS n s).comp (GaS n s).subtype) := by
  classical
  refine ⟨(injective_iff_map_eq_one _).2 ?_, fun g => ?_⟩
  · rintro ⟨x, hx⟩ h1
    refine Subtype.ext (ext_cmp fun w => ?_)
    rw [show ((1 : GaS n s) : Ga l L n) = 1 from rfl, map_one]
    by_cases hw : w.under (𝓞 (Lp L)) ∈ s.St ∨ w.under (𝓞 (Lp L)) = s.v0
    · exact toGS_one s h1 hw
    · exact (mem_GaS s).1 hx w (not_or.1 hw)
  · obtain ⟨x, hx, hx'⟩ := build s hn s.St (fun v hv => split_of s (Or.inl hv))
      fun v => if h : v ∈ s.St then g.1 ⟨v, h⟩ else 1
    obtain ⟨⟨j, hj, hj', -, -⟩, -⟩ := secU l L Ω s n hn (s.w s.v0) (split_of s (Or.inr rfl))
    have hloc : ∀ (u : Plc L), u.under (𝓞 (Lp L)) ≠ s.v0 → cLoc u (j g.2) = 1 := fun u hu =>
      loc_one (hj _) (by rwa [under_w])
    have hS : (away l L n).rangeRestrict (x * j g.2) ∈ GaS n s := by
      refine (mem_GaS s).2 fun w hw => ?_
      by_cases hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal
      · exact cmp_over_l hl _
      · rw [cmp_of hl, map_mul, hx' w hw.1, hloc w hw.2, one_mul]
    refine ⟨⟨_, hS⟩, Prod.ext (funext fun u => ?_) ?_⟩
    · change cmp n (s.w u) ((away l L n).rangeRestrict (x * j g.2)) = g.1 u
      rw [cmp_of (away_of s (Or.inl u.2)), map_mul, hx _ u.2, dite_eq_left u.2,
        hloc _ (by rw [under_w]; exact fun e => s.v0_St (e ▸ u.2)), mul_one]
    · change cmp n (s.w s.v0) ((away l L n).rangeRestrict (x * j g.2)) = g.2
      rw [cmp_of (away_of s (Or.inr rfl)), map_mul, hx' _ (by rw [under_w]; exact s.v0_St), hj', one_mul]

private theorem secS_spec (h : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (g : GS n s) :
    toGS n s (secS n s g) = g ∧ secS n s g ∈ GaS n s := by
  unfold secS
  rw [dite_eq_left h]
  exact ⟨(MulEquiv.ofBijective _ h).apply_symm_apply g, ((MulEquiv.ofBijective _ h).symm g).2⟩

private theorem mem_KS {k : Ga l L n} : k ∈ KS n s ↔ toGS n s k = 1 ∧
    ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → cmp n w k ∈ KO (w.adicCompletion L) (Fin n) := by
  simp only [KS, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap]

private theorem notS {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) :
    w.under (𝓞 (Lp L)) ∉ s.St ∧ w.under (𝓞 (Lp L)) ≠ s.v0 :=
  ⟨fun e => h (Or.inr (Or.inl e)), fun e => h (Or.inr (Or.inr e))⟩

private theorem mem_Ub {x : Ga l L n} : x ∈ Ub n s ↔
    (∀ u : s.St, cmp n (s.w u) x ∈ KO ((s.w u).adicCompletion L) (Fin n)) ∧ cmp n (s.w s.v0) x ∈ Kc _ n 1 := by
  simp only [Ub, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

variable {s}

private theorem mem_UQ {V : s.Lev} (Q : QData V) (hV : V.S' = s.S) {x : Ub n s} : x ∈ UQ n Q ↔
    ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → cmp n w (x : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n) := by
  have hq : ∀ q : Q.Q, False := fun q => Q.notS q (by
    have h : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
      rw [Q.range]
      exact Or.inr ⟨q, rfl⟩
    rwa [hV] at h)
  simp only [UQ, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap, hV]
  exact ⟨fun h => h.1, fun h => ⟨h, fun q => (hq q).elim⟩⟩

end UpperTheory.V.Z.J.D.AuxBlock5

open UpperTheory.V.Z.J.D.AuxBlock5 in
theorem UpperTheory.V.Z.J.D.secSp :
    SecS := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V hV
  have hb := bij s hn
  refine ⟨hb, fun g k hk => comm_of fun w => ?_, fun Q g => ⟨?_, ?_⟩⟩
  · by_cases hw : w.under (𝓞 (Lp L)) ∈ s.St ∨ w.under (𝓞 (Lp L)) = s.v0
    · exact Or.inr (toGS_one s ((mem_KS s).1 hk).1 hw)
    · exact Or.inl ((mem_GaS s).1 (secS_spec s hb g).2 w (not_or.1 hw))
  · rintro ⟨x, hx, rfl⟩
    have hU := (mem_Ub s).1 x.2
    have hs := secS_spec s hb (toGS n s (x : Ga l L n))
    refine ⟨(secS n s (toGS n s (x : Ga l L n)))⁻¹ * x, (mem_KS s).2 ⟨?_, fun w hw => ?_⟩,
      toGS n s (x : Ga l L n), Subgroup.mem_prod.2 ⟨fun u _ => hU.1 u, hU.2⟩, (mul_inv_cancel_left _ _).symm⟩
    · rw [map_mul, map_inv, hs.1, inv_mul_cancel]
    · rw [map_mul, map_inv, (mem_GaS s).1 hs.2 w (notS s hw), inv_one, one_mul]
      exact (mem_UQ Q hV).1 hx w hw
  · rintro ⟨k, hk, p, hp, rfl⟩
    obtain ⟨hk1, hk2⟩ := (mem_KS s).1 hk
    have hs := secS_spec s hb p
    have hU : secS n s p * k ∈ Ub n s := by
      refine (mem_Ub s).2 ⟨fun u => ?_, ?_⟩
      · have e : cmp n (s.w u) (secS n s p) = p.1 u := congrFun (congrArg Prod.fst hs.1) u
        rw [map_mul, e, toGS_one s hk1 (Or.inl (by rw [UpperTheory.V.Z.J.D.AuxBlock5.under_w]; exact u.2)), mul_one]
        exact (Subgroup.mem_prod.1 hp).1 u (Set.mem_univ _)
      · have e : cmp n (s.w s.v0) (secS n s p) = p.2 := congrArg Prod.snd hs.1
        rw [map_mul, e, toGS_one s hk1 (Or.inr (by rw [UpperTheory.V.Z.J.D.AuxBlock5.under_w])), mul_one]
        exact (Subgroup.mem_prod.1 hp).2
    refine ⟨⟨_, hU⟩, (mem_UQ Q hV).2 fun w hw => ?_, rfl⟩
    change cmp n w (secS n s p * k) ∈ _
    rw [map_mul, (mem_GaS s).1 hs.2 w (notS s hw), one_mul]
    exact hk2 w hw
end

