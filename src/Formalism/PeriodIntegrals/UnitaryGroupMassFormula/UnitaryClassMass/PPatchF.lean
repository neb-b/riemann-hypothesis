module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0005

@[expose] public section

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Eps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def adT (T : Set (HeightOneSpectrum (𝓞 F))) : AF F := (show Ainf F × Af F from ((0 : Ainf F), evT T))

theorem adT_idem (T : Set (HeightOneSpectrum (𝓞 F))) : adT T * adT T = adT T := by
  show ((0 : Ainf F), evT T) * ((0 : Ainf F), evT T) = ((0 : Ainf F), evT T)
  exact Prod.ext (mul_zero _) (evT_mul_of_subset (subset_refl T))


variable (E) in
def epsT (T : Set (HeightOneSpectrum (𝓞 F))) : AF F ⊗[F] E := adT T ⊗ₜ[F] (1 : E)

theorem epsT_idem (T : Set (HeightOneSpectrum (𝓞 F))) : epsT E T * epsT E T = epsT E T := by
  unfold epsT
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, adT_idem]

theorem finE_epsT (T : Set (HeightOneSpectrum (𝓞 F))) : finE F E (epsT E T) = evT T ⊗ₜ[F] (1 : E) := by
  unfold epsT
  rw [finE, Algebra.TensorProduct.map_tmul]
  rfl

theorem finE_one_sub_epsT (T : Set (HeightOneSpectrum (𝓞 F))) :
    finE F E (1 - epsT E T) = evT Tᶜ ⊗ₜ[F] (1 : E) := by
  rw [map_sub, map_one, finE_epsT, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
  congr 1
  rw [← evT_compl Tᶜ, compl_compl]

theorem sigR_epsT (σ : E →ₐ[F] E) (T : Set (HeightOneSpectrum (𝓞 F))) : PI.UJClassFin.sigR (AF F) σ (epsT E T) = epsT E T := by
  unfold epsT PI.UJClassFin.sigR
  simp [Algebra.TensorProduct.map_tmul]

end Eps

theorem floc_gmap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (v : HeightOneSpectrum (𝓞 F)) (u : V ≃ₗ[E] V) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ Floc v (gmap u L) ↔ u.symm x ∈ Floc v L := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    rw [mem_gmap_iff] at hsx
    obtain ⟨y, hy, hyx⟩ := hsx
    refine ⟨s, hs, ?_⟩
    rw [← equiv_smul_O u.symm, ← hyx]
    simpa using hy
  · rintro ⟨s, hs, hsx⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff]
    refine ⟨_, hsx, ?_⟩
    rw [equiv_smul_O u, LinearEquiv.apply_symm_apply]

section Localization

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}

private theorem exists_denominator_of_mem_span (L : Submodule (𝓞 E) V) {w : V}
    (hw : w ∈ Submodule.span E (L : Set V)) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ algebraMap (𝓞 F) (𝓞 E) m • w ∈ L := by
  classical
  obtain ⟨n, c, v, rfl⟩ := Submodule.mem_span_set'.1 hw
  obtain ⟨m, hm, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
  refine ⟨(m : 𝓞 F), intCast_ne_zero_OF m hm, ?_⟩
  rw [map_intCast, Int.cast_smul_eq_zsmul (𝓞 E), Finset.smul_sum]
  exact L.sum_mem fun j _ => by
    rw [← smul_assoc]
    exact int_smul_mem L (hint _ (Finset.mem_image_of_mem c (Finset.mem_univ j))) (v j).2

omit [NumberField E] in
private theorem evT_smul_vinc (S : Set (HeightOneSpectrum (𝓞 F))) (y : Fin M → E) :
    (evT S ⊗ₜ[F] (1 : E)) • vinc (F := F) y = fun i => evT S ⊗ₜ[F] y i := by
  funext i
  change (evT S ⊗ₜ[F] (1 : E)) * (1 ⊗ₜ[F] y i) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem mem_span_of_cut_mem_latHat (b : Module.Basis (Fin M) E V)
    (L : Submodule (𝓞 E) V) {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S.Nonempty) {w : V}
    (hw : (evT S ⊗ₜ[F] (1 : E)) • vinc (F := F) (b.equivFun w) ∈ latHat F E (crdOf b L)) :
    w ∈ Submodule.span E (L : Set V) := by
  have hne : evT S ≠ 0 := by
    obtain ⟨v, hv⟩ := hS
    intro h
    have hval := congrArg (fun a : Af F => a v) h
    change evT S v = 0 at hval
    rw [evT_apply, ite_eq_left hv] at hval
    exact one_ne_zero hval
  -- Recover the diagonal vector by applying a functional that sends the selector to one.
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one F hne
  let eval : Af F ⊗[F] E →ₗ[F] E :=
    (TensorProduct.lid F E).toLinearMap.comp (f.rTensor E)
  let pull (y : Fin M → Af F ⊗[F] E) : V := b.equivFun.symm fun i => eval (y i)
  have hpure (a : Af F) (x : Fin M → E) :
      pull (fun i => a ⊗ₜ[F] x i) = algebraMap F E (f a) • b.equivFun.symm x := by
    change b.equivFun.symm (fun i => eval (a ⊗ₜ[F] x i)) = _
    simp only [eval, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul]
    rw [← map_smul]
    congr 1
    funext i
    exact (algebraMap_smul E (f a) (x i)).symm
  have hpull {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E (crdOf b L)) :
      pull y ∈ Submodule.span E (L : Set V) := by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, _, x, hx, rfl⟩ := hy
      rw [hpure]
      apply Submodule.smul_mem _ _ (Submodule.subset_span _)
      exact (mem_iff_crdOf b L _).2 (by simpa only [LinearEquiv.apply_symm_apply] using hx)
    | zero => simp [pull]
    | add y z _ _ hy hz =>
      have hadd : (fun i => eval ((y + z) i)) = (fun i => eval (y i)) + (fun i => eval (z i)) := by
        funext i
        exact map_add eval (y i) (z i)
      simpa only [pull, hadd, map_add] using Submodule.add_mem _ hy hz
    | neg y _ hy =>
      have hneg : (fun i => eval ((-y) i)) = -(fun i => eval (y i)) := by
        funext i
        exact map_neg eval (y i)
      simpa only [pull, hneg, map_neg] using Submodule.neg_mem _ hy
  rw [evT_smul_vinc] at hw
  have h := hpull hw
  simpa [hpure, hf] using h

private theorem flocHat_of_denominator (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    (hsat : ∀ y : Fin M → E, vinc (F := F) y ∈ latHat F E (crdOf b L0) → y ∈ crdOf b L0)
    (S : Set (HeightOneSpectrum (𝓞 F))) (w : V) (mF : 𝓞 F)
    (hmF0 : mF ≠ 0) (hmw : algebraMap (𝓞 F) (𝓞 E) mF • w ∈ L0) :
    (evT S ⊗ₜ[F] (1 : E)) • vinc (F := F) (b.equivFun w) ∈ latHat F E (crdOf b L0) ↔
      ∀ v ∈ S, w ∈ Floc v L0 := by
  classical
  have hmy := (crd_iff b L0 mF w).1 hmw
  have hne : ∀ t : 𝓞 F, t ≠ 0 → algebraMap (𝓞 F) F t ≠ 0 := fun t ht h =>
    ht (FaithfulSMul.algebraMap_injective (𝓞 F) F (by rw [h, map_zero]))
  constructor
  · intro hY v hv
    obtain ⟨t, htv, htint⟩ := t_lemma v mF hmF0
    have key : vinc (F := F) ((algebraMap (𝓞 F) F t) • b.equivFun w) ∈ latHat F E (crdOf b L0) := by
      have hdec : vinc (F := F) ((algebraMap (𝓞 F) F t) • b.equivFun w) =
          (evT {v} ⊗ₜ[F] (1 : E)) • ((algebraMap (𝓞 F) F t) • vinc (F := F) (b.equivFun w)) +
          ((1 - evT {v}) ⊗ₜ[F] (1 : E)) • ((algebraMap (𝓞 F) F t) • vinc (F := F) (b.equivFun w)) := by
        rw [vinc_Fsmul, ← add_smul, ← TensorProduct.add_tmul, add_sub_cancel,
          ← Algebra.TensorProduct.one_def, one_smul]
      rw [hdec]
      apply add_mem
      · rw [tmul_one_smul_Fsmul]
        have e2 : ((evT {v} * algebraMap F (Af F) (algebraMap (𝓞 F) F t)) ⊗ₜ[F] (1 : E)) •
              vinc (F := F) (b.equivFun w) =
            ((evT {v} * algebraMap F (Af F) (algebraMap (𝓞 F) F t)) ⊗ₜ[F] (1 : E)) •
              ((evT S ⊗ₜ[F] (1 : E)) • vinc (F := F) (b.equivFun w)) := by
          rw [tmul_one_smul_smul, mul_right_comm, evT_mul_of_subset (Set.singleton_subset_iff.2 hv)]
        rw [e2]
        exact latHat_smul _ (intAf_mul (evT_int _) (algebraMap_int_intAf t)) hY
      · have e3 : ((1 - evT {v}) ⊗ₜ[F] (1 : E)) • ((algebraMap (𝓞 F) F t) • vinc (F := F) (b.equivFun w)) =
            (((1 - evT {v}) * algebraMap F (Af F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F mF)) ⊗ₜ[F] (1 : E)) •
              vinc (F := F) ((algebraMap (𝓞 F) F mF) • b.equivFun w) := by
          rw [vinc_Fsmul, tmul_one_smul_Fsmul, tmul_one_smul_Fsmul, mul_assoc, ← map_mul,
            div_mul_cancel₀ _ (hne mF hmF0)]
        rw [e3]
        exact latHat_smul _ htint (vinc_mem _ hmy)
    exact ⟨t, htv, (crd_iff b L0 t w).2 (hsat _ key)⟩
  · intro hS
    set B : Set (HeightOneSpectrum (𝓞 F)) := {u | u ∈ S ∧ mF ∈ u.asIdeal} with hB
    have hBfin : B.Finite := (finElt mF hmF0).subset (fun u hu => hu.2)
    have hBS : B ⊆ S := fun u hu => hu.1
    obtain ⟨t, htI, ht0, htB⟩ : ∃ t : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) t • w ∈ L0 ∧ t ≠ 0 ∧
        ∀ u ∈ B, t ∉ u.asIdeal := by
      by_cases hBe : hBfin.toFinset = ∅
      · refine ⟨mF, hmw, hmF0, fun u hu => ?_⟩
        have : u ∈ hBfin.toFinset := (Set.Finite.mem_toFinset _).2 hu
        rw [hBe] at this
        simp at this
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hBe
        let I : Ideal (𝓞 F) := Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) V w) L0)
        have hnot : ¬ ((I : Set (𝓞 F)) ⊆ ⋃ i ∈ (↑hBfin.toFinset : Set (HeightOneSpectrum (𝓞 F))),
            (fun u : HeightOneSpectrum (𝓞 F) => u.asIdeal) i) := by
          rw [Ideal.subset_union_prime a a (fun i _ _ _ => i.isPrime)]
          rintro ⟨u, hu, hIu⟩
          obtain ⟨s, hs, hsw⟩ := hS u ((Set.Finite.mem_toFinset _).1 hu).1
          exact hs (hIu hsw)
        rw [Set.not_subset] at hnot
        obtain ⟨t, htI, htU⟩ := hnot
        have htB : ∀ u ∈ B, t ∉ u.asIdeal := fun u hu hut =>
          htU (Set.mem_biUnion (x := u) ((Set.Finite.mem_toFinset _).2 hu) hut)
        refine ⟨t, htI, fun h => htB a ((Set.Finite.mem_toFinset _).1 ha) (by rw [h]; exact a.asIdeal.zero_mem), htB⟩
    have hty := (crd_iff b L0 t w).1 htI
    have htF := hne t ht0
    rw [evT_split hBS, TensorProduct.add_tmul, add_smul]
    apply add_mem
    · have e1 : evT B = (evT B * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹)) *
          algebraMap F (Af F) (algebraMap (𝓞 F) F t) := by
        rw [mul_assoc, ← map_mul, inv_mul_cancel₀ htF, map_one, mul_one]
      rw [e1, ← tmul_one_smul_Fsmul, ← vinc_Fsmul]
      exact latHat_smul _ (evT_inv_int B t htB) (vinc_mem _ hty)
    · have e1 : evT (S \ B) = (evT (S \ B) * algebraMap F (Af F) ((algebraMap (𝓞 F) F mF)⁻¹)) *
          algebraMap F (Af F) (algebraMap (𝓞 F) F mF) := by
        rw [mul_assoc, ← map_mul, inv_mul_cancel₀ (hne mF hmF0), map_one, mul_one]
      rw [e1, ← tmul_one_smul_Fsmul, ← vinc_Fsmul]
      exact latHat_smul _ (evT_inv_int (S \ B) mF (fun u hu hmu => hu.2 ⟨hu.1, hmu⟩)) (vinc_mem _ hmy)

private theorem flocHat_iff (b : Module.Basis (Fin M) E V) (L : Submodule (𝓞 E) V)
    (hsat : ∀ y : Fin M → E, vinc (F := F) y ∈ latHat F E (crdOf b L) → y ∈ crdOf b L)
    (S : Set (HeightOneSpectrum (𝓞 F))) (w : V) :
    (evT S ⊗ₜ[F] (1 : E)) • vinc (F := F) (b.equivFun w) ∈ latHat F E (crdOf b L) ↔
      ∀ v ∈ S, w ∈ Floc v L := by
  classical
  by_cases hS : S.Nonempty
  · constructor
    · intro hw
      obtain ⟨m, hm, hmw⟩ := exists_denominator_of_mem_span (F := F) L
        (mem_span_of_cut_mem_latHat b L hS hw)
      exact (flocHat_of_denominator b L hsat S w m hm hmw).1 hw
    · intro hw
      obtain ⟨v, hv⟩ := hS
      obtain ⟨m, hm, hmw⟩ := hw v hv
      have hm0 : m ≠ 0 := fun h => hm (h.symm ▸ v.asIdeal.zero_mem)
      exact (flocHat_of_denominator b L hsat S w m hm0 hmw).2 hw
  · have hzero : evT S = 0 := by
      apply af_ext
      intro v
      change evT S v = 0
      rw [evT_apply, ite_eq_right (fun hv => hS ⟨v, hv⟩)]
    rw [hzero]
    simp [Set.not_nonempty_iff_eq_empty.mp hS]

end Localization

theorem local_patching : PatchF := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ M J b L0 _ hsat γ T
  classical
  let ε : AF F ⊗[F] E := epsT E (T : Set (HeightOneSpectrum (𝓞 F)))
  have hε : ε * ε = ε := epsT_idem _
  let e : Bool → AF F ⊗[F] E := fun i => if i then ε else 1 - ε
  have he : ∀ i j, e i * e j = if i = j then e i else 0 := by
    intro i j
    cases i <;> cases j <;> simp only [e, if_true, if_false, Bool.false_eq_true, ↓reduceIte]
    · calc (1 - ε) * (1 - ε) = 1 - ε - (ε - ε * ε) := by ring
        _ = 1 - ε := by rw [hε, sub_self, sub_zero]
    · calc (1 - ε) * ε = ε - ε * ε := by ring
        _ = 0 := by rw [hε, sub_self]
    · calc ε * (1 - ε) = ε - ε * ε := by ring
        _ = 0 := by rw [hε, sub_self]
    · exact hε
  have hs : ∑ i, e i = 1 := by
    rw [Fintype.sum_bool]
    simp only [e, if_true, Bool.false_eq_true, ↓reduceIte]
    abel
  have hσe : ∀ i, PI.UJClassFin.sigR (AF F) σ (e i) = e i := by
    intro i
    cases i <;> simp only [e, if_true, Bool.false_eq_true, ↓reduceIte]
    · rw [map_sub, map_one, sigR_epsT]
    · exact sigR_epsT σ _
  let γB : Bool → GL (Fin M) E := fun i => if i then (γ : GL (Fin M) E) else 1
  have hγB : ∀ i, γB i ∈ PI.UJClassFin.UJ (σ : E →+* E) J := by
    intro i
    cases i
    · exact (PI.UJClassFin.UJ (σ : E →+* E) J).one_mem
    · exact γ.2
  have hf : ∀ i j, finE F E (e i) * finE F E (e j) = if i = j then finE F E (e i) else 0 := by
    intro i j
    rw [← map_mul, he i j]
    split_ifs <;> simp
  have hfe : ∀ i, finE F E (e i) = evT (if i then (T : Set (HeightOneSpectrum (𝓞 F))) else (↑T)ᶜ) ⊗ₜ[F] (1 : E) := by
    intro i
    cases i
    · exact finE_one_sub_epsT _
    · exact finE_epsT _
  have hO : ∀ i, finE F E (e i) ∈ Oh F E := by
    intro i
    rw [hfe i]
    exact tmul_mem_Oh (evT_int _) isIntegral_one
  refine ⟨patchHA σ J e he hs hσe γB hγB, ?_⟩
  ext x
  rw [Set.mem_setOf_eq]
  show (finMat σ J (patchHA σ J e he hs hσe γB hγB)⁻¹).mulVec
      (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (b.equivFun x)) ∈ latHat F E (crdOf b L0) ↔ _
  rw [patch_mulVec, latHat_split (crdOf b L0) (crd_int_smul b L0) _ hf hO, Bool.forall_bool]
  have hterm : ∀ i, (((γB i)⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec (b.equivFun x) =
      b.equivFun ((linOf b (γB i)).symm x) := fun i => (equivFun_linOf_symm b (γB i) x).symm
  rw [hterm, hterm, hfe, hfe]
  have e0 : (linOf b (γB false)).symm x = x := linOf_one_symm_apply b x
  rw [e0, flocHat_iff b L0 hsat, flocHat_iff b L0 hsat]
  have e1 : γB true = (γ : GL (Fin M) E) := rfl
  rw [e1]
  simp only [if_true, Bool.false_eq_true, ↓reduceIte, Set.mem_compl_iff, Finset.mem_coe]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨fun v hv => (floc_gmap v _ L0 x).2 (h1 v hv), h0⟩
  · rintro ⟨h1, h0⟩
    exact ⟨h0, fun v hv => (floc_gmap v _ L0 x).1 (h1 v hv)⟩

theorem surjStep_of_herm (hH : HermApprox) (hO : LSOne) : SurjStep :=
  surjStep_of_patchF_herm local_patching hH hO

end PI.UnitaryGroupMassFormula.UJClassMass

end
