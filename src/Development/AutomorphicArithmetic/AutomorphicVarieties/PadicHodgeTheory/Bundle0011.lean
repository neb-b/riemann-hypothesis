module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartSpan
section
open UpperTheory.V.Loc UpperTheory.V.Alg IsLocalRing

private theorem coeff1_mul {σ E : Type} [CommRing E] (j : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single j 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single j 1) g +
        MvPowerSeries.coeff (Finsupp.single j 1) f * MvPowerSeries.constantCoeff g := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map,
    Finset.Nat.antidiagonal_succ]
  simp

private theorem exists_den {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R]
    [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (x : R →ₐ[O] O) (D : R → E)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = algebraMap O E (x a) * D b + D a * algebraMap O E (x b))
    (halg : ∀ o, D (algebraMap O R o) = 0) :
    ∃ c : O, c ≠ 0 ∧ ∀ a, ∃ o : O, algebraMap O E o = algebraMap O E c * D a := by
  classical
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian (RingHom.ker x) : (RingHom.ker x).FG)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) T D
  refine ⟨c, nonZeroDivisors.ne_zero c.2, ?_⟩
  have h0 : D 0 = 0 := by simpa using halg 0
  have key : ∀ a ∈ Submodule.span R (T : Set R), ∃ o : O, algebraMap O E o = algebraMap O E c * D a := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨o, ho⟩ := hc a ha
      exact ⟨o, by rw [ho, Algebra.smul_def]⟩
    | zero => exact ⟨0, by simp [h0]⟩
    | add a b _ _ ha hb =>
      obtain ⟨o, ho⟩ := ha
      obtain ⟨o', ho'⟩ := hb
      exact ⟨o + o', by rw [map_add (f := _), ho, ho', hadd, mul_add]⟩
    | smul r a ha' ha =>
      obtain ⟨o, ho⟩ := ha
      rw [hT] at ha'
      have hx : x a = 0 := ha'
      exact ⟨x r * o, by rw [map_mul, ho, smul_eq_mul, hmul, hx, map_zero]; ring⟩
  intro a
  have hm : a - algebraMap O R (x a) ∈ RingHom.ker x := by
    simp [RingHom.mem_ker]
  rw [← hT] at hm
  obtain ⟨o, ho⟩ := key _ hm
  refine ⟨o, ?_⟩
  have : D a = D (a - algebraMap O R (x a)) := by
    conv_lhs => rw [← sub_add_cancel a (algebraMap O R (x a))]
    rw [hadd, halg, add_zero]
  rw [this, ho]

private def dualHom {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (x : R →ₐ[O] O) (d : R → O)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = x a * d b + d a * x b)
    (halg : ∀ o, d (algebraMap O R o) = 0) : R →ₐ[O] DualNumber O where
  toFun a := TrivSqZeroExt.inl (x a) + TrivSqZeroExt.inr (d a)
  map_one' := by
    have : d 1 = 0 := by simpa using halg 1
    ext <;> simp [this]
  map_mul' a b := by
    ext <;> simp [hmul, mul_comm]
  map_zero' := by
    have : d 0 = 0 := by simpa using halg 0
    ext <;> simp [this]
  map_add' a b := by
    ext <;> simp [hadd]
  commutes' o := by
    ext <;> simp [halg, TrivSqZeroExt.algebraMap_eq_inl]

private theorem der_zero {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R]
    [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (x : R →ₐ[O] O) (D : R → E)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = algebraMap O E (x a) * D b + D a * algebraMap O E (x b))
    (halg : ∀ o, D (algebraMap O R o) = 0) (S : Type) (e : S → R)
    (hsep : ∀ f f' : R →ₐ[O] DualNumber O, (∀ s, f (e s) = f' (e s)) → f = f')
    (hs : ∀ s, D (e s) = 0) (a : R) : D a = 0 := by
  obtain ⟨c, hc, h⟩ := exists_den x D hadd hmul halg
  choose d hd using h
  have inj := IsFractionRing.injective O E
  have hc' : algebraMap O E c ≠ 0 := fun h => hc (inj (by rw [h, map_zero]))
  have := hsep
    (dualHom x d (fun a b => inj (by rw [map_add (f := _), hd, hd, hd, hadd, mul_add]))
      (fun a b => inj (by rw [map_add (f := _), map_mul, map_mul, hd, hd, hd, hmul]; ring))
      (fun o => inj (by rw [hd, halg, mul_zero, map_zero])))
    (dualHom x (fun _ => 0) (by simp) (by simp) (by simp))
    (fun s => by
      have : d (e s) = 0 := inj (by rw [hd, hs, mul_zero, map_zero])
      ext <;> simp [dualHom, this])
  have h3 : d a = 0 := by
    simpa [dualHom] using congrArg TrivSqZeroExt.snd (DFunLike.congr_fun this a)
  have h4 := hd a
  rw [h3, map_zero] at h4
  exact (mul_eq_zero.mp h4.symm).resolve_left hc'

theorem UpperTheory.V.Loc.chartSpan :
    ∀ {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R] [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (S : Type) (e : S → R), UpperTheory.V.Loc.IsCompl I x φ → (∀ f f' : R →ₐ[O] DualNumber O, (∀ s, f (e s) = f' (e s)) → f = f') → ∃ u : Fin n → S, Submodule.span E (Set.range fun i j : Fin n => MvPowerSeries.coeff (Finsupp.single j 1) (φ (e (u i)))) = ⊤ := by
  intro O R E _ _ _ _ _ _ _ _ n I x φ S e h hsep
  classical
  let L : MvPowerSeries (Fin n) E →ₗ[E] (Fin n → E) :=
    LinearMap.pi fun j => MvPowerSeries.coeff (Finsupp.single j 1)
  have hL : ∀ f j, L f j = MvPowerSeries.coeff (Finsupp.single j 1) f := fun _ _ => rfl
  have hLmul : ∀ f g, L (f * g) = MvPowerSeries.constantCoeff f • L g + MvPowerSeries.constantCoeff g • L f := by
    intro f g
    funext j
    simp only [hL, coeff1_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hm2 : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2, L f = 0 := by
    have hm : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) E), MvPowerSeries.constantCoeff f = 0 := by
      intro f hf
      by_contra hne
      exact hf (MvPowerSeries.isUnit_iff_constantCoeff.mpr (Ne.isUnit hne))
    intro f hf
    rw [pow_two] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      rw [hLmul, hm a ha, hm b hb]; simp
    · intro a b ha hb
      rw [map_add (f := _), ha, hb, add_zero]
  have hspan : Submodule.span E (Set.range fun s => L (φ (e s))) = ⊤ := by
    by_contra hne
    obtain ⟨lam, hlam, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hD := der_zero x (fun a => lam (L (φ a))) (fun a b => by simp)
      (fun a b => by
        rw [map_mul, hLmul, h.const, h.const]
        simp only [map_add (f := _), map_smul, smul_eq_mul]
        ring)
      (fun o => by
        have : L (φ (algebraMap O R o)) = 0 := by
          funext j
          rw [AlgHom.commutes, hL, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
          simp
        rw [this, map_zero])
      S e hsep (fun s => hker (Submodule.subset_span ⟨s, rfl⟩))
    apply hlam
    refine (Pi.basisFun E (Fin n)).ext fun j => ?_
    obtain ⟨a, c, hc, hca⟩ := h.dense 2 (MvPowerSeries.X j)
    have h1 := hm2 _ hca
    have hX : L (MvPowerSeries.X j) = Pi.basisFun E (Fin n) j := by
      funext i
      rw [hL, MvPowerSeries.coeff_index_single_X]
      simp [Pi.single_apply]
    rw [map_sub, ← algebraMap_smul E c, map_smul, hX, sub_eq_zero] at h1
    have h2 := hD a
    simp only [← h1, map_smul, smul_eq_mul] at h2
    have hc' : algebraMap O E c ≠ 0 := fun h => hc (IsFractionRing.injective O E (by rw [h, map_zero]))
    exact (mul_eq_zero.mp h2).resolve_left hc'
  obtain ⟨b, hb, hbs, hbi⟩ := exists_linearIndependent E (Set.range fun s => L (φ (e s)))
  rw [hspan] at hbs
  have hfin : b.Finite := hbi.set_finite_of_isNoetherian
  haveI := hfin.fintype
  let B : Module.Basis b E (Fin n → E) := Module.Basis.mk hbi (by simp [hbs])
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis B]; simp
  let q : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  choose u hu using fun i : Fin n => hb (q i).2
  refine ⟨u, ?_⟩
  rw [eq_top_iff, ← hbs]
  refine Submodule.span_mono fun v hv => ⟨q.symm ⟨v, hv⟩, ?_⟩
  have := hu (q.symm ⟨v, hv⟩)
  rw [Equiv.apply_symm_apply] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CocycleTransportH1fSurjective
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc.BlochKatoDimension

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {K : FinExt l} (e : G ≃* ↥(GK K))
  {E : Type} [Field E] [Algebra ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] E V] (ρ : Representation E G V)

private def tr : Representation ℚ_[l] ↥(GK K) V := (resCoef ℚ_[l] ρ).comp e.symm.toMonoidHom

private theorem tr_apply (g : G) (v : V) : tr e ρ (e g) v = ρ g v := by
  simp [tr, resCoef]

private theorem actVB_tr (g : G) (x : V ⊗[ℚ_[l]] Bcr l) :
    actVB ((PP l).PD K) (tr e ρ) (e g) x = actC ((GK K).subtype.comp e.toMonoidHom) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, actC, tr_apply, (PP l).PD_actB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem actVdR_tr (g : G) (x : V ⊗[ℚ_[l]] Bdr l) :
    actVdR ((PP l).PD K) (tr e ρ) (e g) x = actD ((GK K).subtype.comp e.toMonoidHom) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, actD, tr_apply, (PP l).PD_actdR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem actD_res (φ : G →* GQ l) (g : G) (x : V ⊗[ℚ_[l]] Bdr l) :
    actD φ (resCoef ℚ_[l] ρ) g x = actD φ ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actD, resCoef]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem Ddr_res (φ : G →* GQ l) :
    Ddr φ (resCoef ℚ_[l] ρ) = (Ddr φ ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [Ddr, sub_eq_zero, actD_res]

private theorem DdR_tr :
    DdR ((PP l).PD K) (tr e ρ) = (Ddr ((GK K).subtype.comp e.toMonoidHom) ρ).restrictScalars ℚ_[l] := by
  ext x
  simp only [DdR, Ddr, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply]
  rw [e.surjective.forall]
  simp only [actVdR_tr]

private theorem h0V_tr_eq_restrictScalars_h0 : H0V (tr e ρ) = (H0 ρ).restrictScalars ℚ_[l] := by
  ext x
  simp only [H0V, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, H0, Representation.mem_invariants]
  rw [e.surjective.forall]
  simp only [tr_apply]

variable (K E V) in
private theorem FilV_eq (a : ℤ) :
    FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a =
      (UpperTheory.V.Loc.FilT (l := l) E V a).restrictScalars ℚ_[l] := by
  have hF : (((PP l).PD K).Fil a).restrictScalars ℚ_[l] =
      (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l] :=
    SetLike.coe_injective ((PP l).PD_Fil K (botExt l) a)
  have h : ∀ (N : Submodule ℚ_[l] (Bdr l)) y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V)
      N.subtype y = AlgebraTensorModule.map (LinearMap.id : V →ₗ[E] V) N.subtype y := by
    intro N y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  ext x
  rw [FilV, hF]
  simp only [UpperTheory.V.Loc.FilT, Submodule.restrictScalars_mem, LinearMap.mem_range, h]

variable [TopologicalSpace G] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V]
  [ContinuousConstSMul ℚ_[l] V]

private theorem mem_Z1f_transport_iff (he : Continuous e) (he' : Continuous e.symm) (c : ↥(GK K) → V) :
    c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ) ↔
      (c ∘ e) ∈ UpperTheory.V.Loc.finiteCocycles ((GK K).subtype.comp e.toMonoidHom) ρ := by
  show ((Continuous c ∧ ∀ g h, c (g * h) = c g + tr e ρ g (c h)) ∧
      ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actVB ((PP l).PD K) (tr e ρ) g x - x) ↔
    ((Continuous (c ∘ e) ∧ ∀ g h, c (e (g * h)) = c (e g) + ρ g (c (e h))) ∧
      ∃ x, ∀ g, c (e g) ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actC ((GK K).subtype.comp e.toMonoidHom) ρ g x - x)
  refine and_congr (and_congr ⟨fun h => h.comp he, fun h => ?_⟩ ?_) (exists_congr fun x => ?_)
  · simpa only [Function.comp_def, MulEquiv.apply_symm_apply] using h.comp he'
  · rw [e.surjective.forall₂]
    simp only [tr_apply, map_mul]
  · rw [e.surjective.forall]
    simp only [actVB_tr]

private def cocycleTransportToH1f (he : Continuous e) (he' : Continuous e.symm) :
    ↥(Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ)) →ₗ[ℚ_[l]] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) where
  toFun c := ⟨Submodule.Quotient.mk ⟨c.1 ∘ e, ((mem_Z1f_transport_iff e ρ he he' c.1).mp c.2).1⟩,
    ⟨_, (mem_Z1f_transport_iff e ρ he he' c.1).mp c.2, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem cocycle_transport_H1f_surjective (he : Continuous e) (he' : Continuous e.symm) :
    Function.Surjective (cocycleTransportToH1f e ρ he he') := by
  rintro ⟨_, c, hc, rfl⟩
  have h : (c.1 ∘ e.symm) ∘ e = c.1 := by
    funext g
    simp
  refine ⟨⟨c.1 ∘ e.symm, (mem_Z1f_transport_iff e ρ he he' _).mpr (by rw [h]; exact hc)⟩, Subtype.ext ?_⟩
  exact congrArg Submodule.Quotient.mk (Subtype.ext h)

private theorem ker_cocycle_transport_H1f (he : Continuous e) (he' : Continuous e.symm) :
    LinearMap.ker (cocycleTransportToH1f e ρ he he') =
      (Formalism.WeaklyAdmissibleFiltrations.B1 (tr e ρ)).comap (Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) (tr e ρ)).subtype := by
  ext c
  rw [LinearMap.mem_ker, Subtype.ext_iff]
  refine (Submodule.Quotient.mk_eq_zero _).trans ?_
  refine (mem_coboundaries1 ρ (c.1 ∘ e)).trans ?_
  refine exists_congr fun m => ?_
  show (∀ g, c.1 (e g) = ρ g m - m) ↔ (fun g => tr e ρ g m - m) = c.1
  rw [funext_iff, e.surjective.forall]
  simp only [tr_apply]
  exact forall_congr' fun g => eq_comm

private def h1fEquiv (he : Continuous e) (he' : Continuous e.symm) :
    FiniteCohomology ((PP l).PD K) (tr e ρ) ≃ₗ[ℚ_[l]] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) :=
  (Submodule.quotEquivOfEq _ _ (ker_cocycle_transport_H1f e ρ he he').symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (cocycle_transport_H1f_surjective e ρ he he'))

end UpperTheory.V.Loc.BlochKatoDimension

open UpperTheory.V.Loc.BlochKatoDimension in
theorem UpperTheory.V.Loc.bkDim :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → IsDr φ ρ → Module.Finite E ↥(finiteCohomology φ ρ) ∧
      finrank E ↥(finiteCohomology φ ρ) + finrank E ↥(UpperTheory.V.Loc.FilD φ ρ 0) =
        finrank E ↥(H0 ρ) + φ.range.index * finrank E V := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ V _ _ _ _ _ _ _ _ _ ρ hc hdR
  obtain ⟨K, e, he, he', hφe, -, hind, -⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  rw [IsDr, hind, Ddr_res] at hdR
  rw [hind]
  clear hind hφ
  subst hφe
  have hD := (hP.bk l (PP l) (AIP l) T K).1
  have hcont : ∀ x, Continuous fun g => tr e ρ g x := fun x =>
    hc.comp (he'.prodMk continuous_const)
  have hdR' : IsDR ((PP l).PD K) (tr e ρ) := by
    rw [IsDR, DdR_tr]
    exact hdR
  obtain ⟨hfin, hdim⟩ := hD V (tr e ρ) hcont hdR'
  haveI : Module.Finite ℚ_[l] ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) :=
    Module.Finite.equiv (h1fEquiv e ρ he he')
  refine ⟨Module.Finite.of_restrictScalars_finite ℚ_[l] E _, ?_⟩
  have hH1 : finrank ℚ_[l] (FiniteCohomology ((PP l).PD K) (tr e ρ)) =
      finrank ℚ_[l] E * finrank E ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) := by
    rw [(h1fEquiv e ρ he he').finrank_eq, finrank_mul_finrank]
  have hH0 : finrank ℚ_[l] ↥(H0V (tr e ρ)) = finrank ℚ_[l] E * finrank E ↥(H0 ρ) := by
    rw [h0V_tr_eq_restrictScalars_h0, finrank_mul_finrank]
    rfl
  have hF : finrank ℚ_[l] ↥(DdR ((PP l).PD K) (tr e ρ) ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) 0) =
      finrank ℚ_[l] E * finrank E ↥(UpperTheory.V.Loc.FilD ((GK K).subtype.comp e.toMonoidHom) ρ 0) := by
    rw [DdR_tr, FilV_eq K E V, ← Submodule.restrictScalars_inf, finrank_mul_finrank]
    rfl
  rw [IsDR, ← finrank_mul_finrank ℚ_[l] E V] at hdR'
  rw [hH1, hH0, hdR', hF] at hdim
  have hd : (finrank ℚ_[l] E : ℤ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ_[l]) (M := E)).ne'
  push_cast at hdim
  have : ((finrank E ↥(finiteCohomology ((GK K).subtype.comp e.toMonoidHom) ρ) +
      finrank E ↥(UpperTheory.V.Loc.FilD ((GK K).subtype.comp e.toMonoidHom) ρ 0) : ℕ) : ℤ) =
      ((finrank E ↥(H0 ρ) + finrank ℚ_[l] ↥K.1 * finrank E V : ℕ) : ℤ) := by
    push_cast
    refine mul_left_cancel₀ hd ?_
    linear_combination hdim
  exact_mod_cast this

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
section
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

private theorem de_mem {Ω : Type} [Field Ω] {v : ℕ} [Fact v.Prime] (j : Ω →+* Om v) (x : Ω) :
    x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := by
  rw [placeJ, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def,
    ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

private theorem de_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {v : ℕ} [Fact v.Prime] {A : ValuationSubring Ω} {j : Ω →+* Om v} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (g : ↥(Dec (F := F) A)) (σ : GQ v) (hi : ∀ y, σ (j y) = j ((g : G F Ω) y)) :
    σ ∈ Iq v ↔ (g : G F Ω) ∈ Ine (F := F) A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hnorm : ∀ y, ‖j y‖ < 1 ↔ A.valuation y < 1 := GlobalTheory.DecLocal.norm_lt_one_iff A j hj
  have hle : ∀ y, A.valuation y ≤ 1 ↔ ‖j y‖ ≤ 1 := fun y => by
    rw [A.valuation_le_one_iff y, hj]
  rw [(iqBasic v).2.2.1 σ]
  change _ ↔ (g : G F Ω) ∈ ValuationSubring.decompositionSubgroup F A ∧
    ∀ x, A.valuation x ≤ 1 → A.valuation ((g : G F Ω) x - x) < 1
  constructor
  · intro h
    refine ⟨g.2, fun x hx => ?_⟩
    rw [← hnorm, map_sub, ← hi]
    exact h (j x) ((hle x).mp hx)
  · rintro ⟨-, h⟩ y hy
    obtain ⟨x, hx⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt y one_pos
    rw [dist_eq_norm] at hx
    have hjx : ‖j x‖ ≤ 1 := by
      have hm := IsUltrametricDist.norm_add_le_max y (-(y - j x))
      rw [norm_neg, ← sub_eq_add_neg, sub_sub_cancel] at hm
      exact hm.trans (max_le hy hx.le)
    have h3 : ‖σ (j x) - j x‖ < 1 := by
      rw [hi, ← map_sub, hnorm]
      exact h x ((hle x).mpr hjx)
    have hdecomp : σ y - y = (σ (y - j x) - (y - j x)) + (σ (j x) - j x) := by
      rw [map_sub]
      ring
    have h1 : ‖σ (y - j x)‖ < 1 := by
      rw [GlobalTheory.PlaceBridge.norm_algEquiv]
      exact hx
    have h5 : ‖σ (y - j x) - (y - j x)‖ < 1 := by
      have hm := IsUltrametricDist.norm_add_le_max (σ (y - j x)) (-(y - j x))
      rw [norm_neg, ← sub_eq_add_neg] at hm
      exact lt_of_le_of_lt hm (max_lt h1 hx)
    rw [hdecomp]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h5 h3)

private theorem de_cyc {F Ω : Type} [Field F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosed Ω]
    {v : ℕ} [Fact v.Prime] {j : Ω →+* Om v} (l : ℕ) [Fact l.Prime]
    (g : G F Ω) (σ : GQ v) (hi : ∀ y, σ (j y) = j (g y)) :
    UpperTheory.V.Loc.cyc v l σ = cycZ F Ω l g := by
  have hjinj : Function.Injective j := j.injective
  simp only [UpperTheory.V.Loc.cyc, ReciprocityTheory.Gal.cycZ, MonoidHom.comp_apply]
  apply Units.ext
  apply (PadicInt.ext_of_toZModPow).mp
  intro n
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have h1 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one
  have h2 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ v) (Om v) σ) (j ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  rw [show (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ = g ζ from rfl] at h1
  rw [show (MulSemiringAction.toRingAut (GQ v) (Om v) σ) (j ζ) = σ (j ζ) from rfl] at h2
  rw [hi, h1, ← map_pow] at h2
  have h4 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hjinj h2)
  exact (ZMod.val_injective _ h4).symm

theorem UpperTheory.V.Loc.decEmb :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {v : ℕ} [Fact v.Prime], (∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)), IsPlaceOver A w → ((v : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ j : Ω →+* Om v, placeJ j = A) ∧ ∀ j : Ω →+* Om v, (∃ w : HeightOneSpectrum (𝓞 F), IsPlaceOver (placeJ j) w ∧ ((v : ℕ) : 𝓞 F) ∈ w.asIdeal) ∧ ∃ φ : ↥(Dec (F := F) (placeJ j)) →* GQ v, IsOpenEmbedding φ ∧ (∀ g y, φ g (j y) = j ((g : G F Ω) y)) ∧ (∀ σ : GQ v, σ ∈ φ.range ↔ ∀ x : F, σ (j (algebraMap F Ω x)) = j (algebraMap F Ω x)) ∧ (∀ g, φ g ∈ Iq v ↔ (g : G F Ω) ∈ Ine (F := F) (placeJ j)) ∧ (∀ (l : ℕ) [Fact l.Prime] g, UpperTheory.V.Loc.cyc v l (φ g) = cycZ F Ω l (g : G F Ω)) ∧ ∀ w : HeightOneSpectrum (𝓞 F), IsPlaceOver (placeJ j) w → φ.range.index = locDeg w := by
  intro F Ω _ _ _ _ _ _ v _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  refine ⟨?_, ?_⟩
  · intro A w hA hw
    obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := v) F Ω w A hw hA
    refine ⟨j, ?_⟩
    ext x
    rw [de_mem, hj]
  · intro j
    have hj : ∀ x, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := de_mem j
    refine ⟨?_, ?_⟩
    · have hlt : (placeJ j).valuation ((v : ℕ) : Ω) < 1 := by
        rw [← GlobalTheory.DecLocal.norm_lt_one_iff _ j hj, map_natCast]
        exact GlobalTheory.PlaceBridge.norm_l_lt_one
      obtain ⟨w, hw, hpo⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := F) (placeJ j) hlt
      exact ⟨w, hpo, hw⟩
    · let K : FinExt v := ⟨IntermediateField.adjoin ℚ_[v] (Set.range fun x => j (algebraMap F Ω x)),
        GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
      haveI : FiniteDimensional ℚ_[v] (K : IntermediateField ℚ_[v] (Om v)) := K.2
      have hK : (K : IntermediateField ℚ_[v] (Om v)) =
          IntermediateField.adjoin ℚ_[v] (Set.range fun x => j (algebraMap F Ω x)) := rfl
      obtain ⟨e, hec, hesc, he⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K hK
      let φ : ↥(Dec (F := F) (placeJ j)) →* GQ v := (GK K).subtype.comp e.toMonoidHom
      have hφ : ∀ g, φ g = (e g : GQ v) := fun g => rfl
      have hrange : ∀ σ : GQ v, σ ∈ φ.range ↔ σ ∈ GK K := by
        intro σ
        constructor
        · rintro ⟨g, rfl⟩
          exact (e g).2
        · intro h
          exact ⟨e.symm ⟨σ, h⟩, by rw [hφ, MulEquiv.apply_symm_apply]⟩
      have hopen : IsOpen ((GK K : Subgroup (GQ v)) : Set (GQ v)) :=
        IntermediateField.fixingSubgroup_isOpen (K : IntermediateField ℚ_[v] (Om v))
      refine ⟨φ, ?_, fun g y => he g y, fun σ => by rw [hrange, GlobalTheory.PlaceBridge.mem_GK_iff (E := F) K hK],
        fun g => de_ine hj g (φ g) (he g), fun l _ g => de_cyc l (g : G F Ω) (φ g) (he g), fun w hw => ?_⟩
      · let h : ↥(Dec (F := F) (placeJ j)) ≃ₜ ↥(GK K) :=
          { e.toEquiv with continuous_toFun := hec, continuous_invFun := hesc }
        exact hopen.isOpenEmbedding_subtypeVal.comp h.isOpenEmbedding
      · have hr : φ.range = GK K := by
          ext σ
          exact hrange σ
        rw [hr, ← GlobalTheory.DecLocal.finrank_closure_eq_locDeg v F Ω (placeJ j) j hj w hw,
          IntermediateField.finrank_eq_fixingSubgroup_index]
        rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fCoef
section
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

theorem UpperTheory.V.Loc.z1fCoef :
    ∀ {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l) {A A' V V' : Type} [CommRing A] [Algebra ℚ_[l] A] [CommRing A'] [Algebra ℚ_[l] A'] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A H V) (ρ' : Representation A' H V') (f : V →ₗ[ℚ_[l]] V'), Continuous f → (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c ∈ finiteCocycles φ ρ, (fun g => f (c g)) ∈ finiteCocycles φ ρ' := by
  intro l _ H _ _ φ A A' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ ρ' f hfc hf c hc
  obtain ⟨⟨hc, hcc⟩, x, hx⟩ := hc
  refine ⟨⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Bcr l) f x, fun g => ?_⟩
  · simp only [hcc g h, map_add (f := _), hf]
  · have key : ∀ y : TensorProduct ℚ_[l] V (Bcr l), LinearMap.rTensor (Bcr l) f (actC φ ρ g y) =
        actC φ ρ' g (LinearMap.rTensor (Bcr l) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [actC, hf]
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
end

