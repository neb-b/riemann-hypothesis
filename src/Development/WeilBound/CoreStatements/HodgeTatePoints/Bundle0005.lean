module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PfibRing
section
open TensorProduct LinearMap IsLocalRing

namespace PositivityTheory.HtPt.Pfib

open GlobalTheory.LocalFlat

theorem lTensor_map_injective {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    (p : Ideal R) :
    Function.Injective ((p.map (algebraMap R A)).subtype.lTensor M) := by
  let I := p.map (algebraMap R A)
  let c : p →ₗ[R] I :=
    { toFun := fun r => ⟨algebraMap R A r, Ideal.mem_map_of_mem _ r.2⟩
      map_add' := fun r s => Subtype.ext (by simp)
      map_smul' := fun r s => Subtype.ext (by simp [Algebra.smul_def]) }
  let φ : M ⊗[R] p →ₗ[R] M ⊗[A] I :=
    TensorProduct.mapOfCompatibleSMul A R R M I ∘ₗ c.lTensor M
  have hφ : ∀ m r, φ (m ⊗ₜ r) = m ⊗ₜ[A] c r := fun _ _ => rfl
  have hsurj : ∀ x, x ∈ LinearMap.range φ := by
    intro x
    induction x with
    | add a b ha hb => exact add_mem ha hb
    | tmul m i =>
      obtain ⟨i, hi⟩ := i
      induction hi using Submodule.span_induction generalizing m with
      | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        exact ⟨m ⊗ₜ ⟨r, hr⟩, rfl⟩
      | zero =>
        change m ⊗ₜ[A] (0 : I) ∈ _
        rw [tmul_zero]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        change m ⊗ₜ[A] ((⟨x, hx⟩ : I) + ⟨y, hy⟩) ∈ _
        rw [tmul_add]
        exact add_mem (ihx m) (ihy m)
      | smul a x hx ih =>
        change m ⊗ₜ[A] (a • (⟨x, hx⟩ : I)) ∈ _
        rw [← smul_tmul]
        exact ih _
  have hcomp : ∀ y, TensorProduct.rid A M (I.subtype.lTensor M (φ y)) =
      TensorProduct.rid R M (p.subtype.lTensor M y) := by
    intro y
    induction y with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul m r => simp [hφ, c]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have h0 := hcomp y
  rw [hx, map_zero, eq_comm, map_eq_zero_iff _ (TensorProduct.rid R M).injective,
    map_eq_zero_iff _ (Module.Flat.lTensor_preserves_injective_linearMap p.subtype
      p.injective_subtype)] at h0
  rw [h0, map_zero]

section Devissage

variable {A : Type} [CommRing A] {M : Type} [AddCommGroup M] [Module A M]

theorem exists_of_lTensor_eq {F G N : Type} [AddCommGroup F] [Module A F] [AddCommGroup G]
    [Module A G] [AddCommGroup N] [Module A N] (f : F →ₗ[A] N) (g : G →ₗ[A] N)
    (hs : Function.Surjective (f.coprod g)) (x : M ⊗[A] F) (y : M ⊗[A] G)
    (h : f.lTensor M x + g.lTensor M y = 0) :
    ∃ z : M ⊗[A] ker (f.coprod g),
      (fst A F G ∘ₗ (ker (f.coprod g)).subtype).lTensor M z = x ∧
      (snd A F G ∘ₗ (ker (f.coprod g)).subtype).lTensor M z = y := by
  have hex := lTensor_exact M (f.coprod g).exact_subtype_ker_map hs
  have h0 : (f.coprod g).lTensor M ((inl A F G).lTensor M x + (inr A F G).lTensor M y) = 0 := by
    rw [map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply, coprod_inl, coprod_inr, h]
  obtain ⟨z, hz⟩ := (hex _).mp h0
  refine ⟨z, ?_, ?_⟩
  · rw [lTensor_comp_apply, hz, map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply,
      fst_comp_inl, fst_comp_inr]
    simp
  · rw [lTensor_comp_apply, hz, map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply,
      snd_comp_inl, snd_comp_inr]
    simp

theorem lTensor_injective_of_le_range {I : Ideal A} (hrel : RelationsLift I M)
    (hI : Function.Injective (I.subtype.lTensor M)) {F : Type} [AddCommGroup F] [Module A F]
    (f : F →ₗ[A] A) (hf : Function.Injective f) (hle : I ≤ range f) :
    Function.Injective (f.lTensor M) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel F f x (by rw [hx]; simp)
  let e₀ : Submodule.comap f I →ₗ[A] I := f.restrict fun _ h => h
  have he : Function.Bijective e₀ := by
    refine ⟨fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab)), fun i => ?_⟩
    obtain ⟨a, ha⟩ := hle i.2
    exact ⟨⟨a, by rw [Submodule.mem_comap, ha]; exact i.2⟩, Subtype.ext ha⟩
  let e := LinearEquiv.ofBijective e₀ he
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← lTensor_comp_apply, ← lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ hI] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

theorem lTensor_injective_of_pow_le [IsNoetherianRing A] {I : Ideal A} (hrel : RelationsLift I M)
    (hI : Function.Injective (I.subtype.lTensor M)) (n : ℕ) (J : Ideal A) (hJ : I ^ n ≤ J) :
    Function.Injective (J.subtype.lTensor M) := by
  induction J using WellFoundedGT.induction with
  | ind J ih =>
  by_cases hex : ∃ a, a ∉ J ∧ ∀ i ∈ I, i * a ∈ J
  · obtain ⟨a, ha, hIa⟩ := hex
    let J' : Ideal A := J ⊔ Ideal.span {a}
    have haJ' : a ∈ J' := Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < J' := lt_of_le_of_ne le_sup_left fun h => ha (h ▸ haJ')
    have h' := ih J' hlt (hJ.trans hlt.le)
    let f : J →ₗ[A] J' := Submodule.inclusion hlt.le
    let g : A →ₗ[A] J' := toSpanSingleton A J' ⟨a, haJ'⟩
    have hs : Function.Surjective (f.coprod g) := by
      rintro ⟨b, hb⟩
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      exact ⟨(⟨j, hj⟩, c), rfl⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hfx : f.lTensor M x = 0 := by
      apply h'
      rw [← lTensor_comp_apply, map_zero]
      exact hx
    obtain ⟨z, hz1, hz2⟩ := exists_of_lTensor_eq f g hs x 0 (by rw [hfx, map_zero, add_zero])
    have hinj : Function.Injective
        ((snd A J A ∘ₗ (ker (f.coprod g)).subtype).lTensor M) := by
      refine lTensor_injective_of_le_range hrel hI _ ?_ fun i hi => ?_
      · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
        rintro ⟨⟨j, c⟩, hjc⟩ hc
        have hc' : c = 0 := hc
        subst hc'
        have h1 : (j : A) + (0 : A) • a = 0 := congrArg Subtype.val hjc
        have h2 : j = 0 := Subtype.ext (by simpa using h1)
        subst h2
        rfl
      · refine ⟨⟨(⟨-(i * a), neg_mem (hIa i hi)⟩, i), ?_⟩, rfl⟩
        refine Subtype.ext ?_
        change -(i * a) + i • a = 0
        simp
    have hz : z = 0 := hinj (hz2.trans (map_zero _).symm)
    rw [← hz1, hz, map_zero]
  · push Not at hex
    have htop : ∀ m : ℕ, I ^ m ≤ J → (1 : A) ∈ J := by
      intro m
      induction m with
      | zero => intro h; exact h (by simp)
      | succ m ihm =>
        intro h
        refine ihm fun a ha => ?_
        by_contra haJ
        obtain ⟨i, hi, hia⟩ := hex a haJ
        exact hia (h (by rw [pow_succ']; exact Ideal.mul_mem_mul hi ha))
    refine lTensor_injective_of_le_range hrel hI _ J.injective_subtype ?_
    rw [Submodule.range_subtype, (Ideal.eq_top_iff_one J).mpr (htop n hJ)]
    exact le_top

theorem relationsLift_of_injective {J : Ideal A}
    (h : ∀ J' : Ideal A, J ≤ J' → Function.Injective (J'.subtype.lTensor M)) :
    RelationsLift J M := by
  intro F _ _ f x hx
  have hy : ∀ m ∈ J • (⊤ : Submodule A M),
      ∃ y : M ⊗[A] J, TensorProduct.rid A M (J.subtype.lTensor M y) = m := by
    intro m hm
    induction hm using Submodule.smul_induction_on' with
    | smul r hr m _ => exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩
    | add a _ b _ ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', by simp⟩
  obtain ⟨y, hy⟩ := hy _ hx
  have hy' := (TensorProduct.rid A M).injective hy
  let J' : Ideal A := range f ⊔ J
  let f' : F →ₗ[A] J' := f.codRestrict J' fun a => Submodule.mem_sup_left ⟨a, rfl⟩
  let g : J →ₗ[A] J' := Submodule.inclusion le_sup_right
  have hs : Function.Surjective (f'.coprod g) := by
    rintro ⟨b, hb⟩
    obtain ⟨_, ⟨a, rfl⟩, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
    exact ⟨(a, ⟨c, hc⟩), rfl⟩
  have h0 : f'.lTensor M x + g.lTensor M (-y) = 0 := by
    apply h J' le_sup_right
    rw [map_add (f := _), ← lTensor_comp_apply, ← lTensor_comp_apply, map_zero, map_neg]
    change f.lTensor M x + -(J.subtype.lTensor M y) = 0
    rw [hy', add_neg_cancel]
  obtain ⟨z, hz, -⟩ := exists_of_lTensor_eq f' g hs x (-y) h0
  refine range_lTensor_le _ _ ?_ ⟨z, hz⟩
  rintro ⟨⟨a, j⟩, haj⟩
  have h1 : f a + (j : A) = 0 := congrArg Subtype.val haj
  change f a ∈ J
  rw [eq_neg_of_add_eq_zero_left h1]
  exact neg_mem j.2

theorem flat_of_relationsLift_of_injective [IsNoetherianRing A] (B : Type) [CommRing B]
    [Algebra A B] [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    {I : Ideal A} (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥) (hrel : RelationsLift I M)
    (hinj : Function.Injective (I.subtype.lTensor M)) : Module.Flat A M :=
  flat_of_relationsLift B hI fun n =>
    relationsLift_of_injective fun J hJ => lTensor_injective_of_pow_le hrel hinj n J hJ

end Devissage

theorem fibre_crit_ring : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)], Module.Flat R B → (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) (IsScalarTower.toAlgHom R A B)).toRingHom.Flat → Module.Flat A B := by
  intro R A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB h
  refine flat_of_relationsLift_of_injective B (I := (maximalIdeal R).map (algebraMap R A)) ?_ ?_
    (lTensor_map_injective _)
  · exact ((Ideal.map_mono (map_maximalIdeal_le _)).trans (map_maximalIdeal_le _)).trans
      (maximalIdeal_le_jacobson _)
  · refine relationsLift_of_square
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] ResidueField R ⊗[R] A) :
        A →+* ResidueField R ⊗[R] A)
      ((Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) :
        B →+* ResidueField R ⊗[R] B) _
      (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
      (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
      (GlobalTheory.ker_includeRight_quotient A (maximalIdeal R)) ?_ ?_ h
    · rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      exact GlobalTheory.ker_includeRight_quotient B (maximalIdeal R)
    · ext a
      simp

end PositivityTheory.HtPt.Pfib
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Twhopf

theorem translate_mem : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := by
  intro R _ T _ A hA f hf t
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      have e : (fun h => a (t, h).1 * b (t, h).2) = a t • b := by
        funext h
        simp [smul_eq_mul]
      rw [e]
      exact A.smul_mem hb _
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)

theorem exists_coset_coord {T H : Type} [CommGroup T] [CommGroup H] (ι : H →* T) :
    ∃ κ : T → H, ∀ t, (QuotientGroup.mk t : T ⧸ ι.range).out * ι (κ t) = t := by
  have key : ∀ t : T, ∃ h : H, ι h = ((QuotientGroup.mk t : T ⧸ ι.range).out)⁻¹ * t := fun t =>
    MonoidHom.mem_range.mp (QuotientGroup.eq.mp (QuotientGroup.out_eq' _))
  choose κ hκ using key
  exact ⟨κ, fun t => by rw [hκ, mul_inv_cancel_left]⟩

theorem ind_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (H : Type) [CommGroup H] (ι : H →* T), Function.Injective ι → ∀ A : Subalgebra R (H → R), IsHopfOrder A → IsHopfOrder (indOrder ι A) := by
  classical
  intro R _ _ T _ _ H _ ι hι A hA
  have : Fintype (T ⧸ ι.range) := Fintype.ofFinite _
  have : Module.Finite R A := hA.finite
  have : Module.Projective R A := hA.projective
  obtain ⟨κ, hκ⟩ := exists_coset_coord ι
  have hmk : ∀ t h, (QuotientGroup.mk (t * ι h) : T ⧸ ι.range) = QuotientGroup.mk t := by
    intro t h
    rw [QuotientGroup.eq]
    exact MonoidHom.mem_range.mpr ⟨h⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  have hκmul : ∀ t h, κ (t * ι h) = κ t * h := by
    intro t h
    apply hι
    have e1 := hκ (t * ι h)
    have e2 := hκ t
    rw [hmk] at e1
    rw [map_mul]
    apply mul_left_cancel (a := (QuotientGroup.mk t : T ⧸ ι.range).out)
    rw [e1, ← mul_assoc, e2]
  let ext : T ⧸ ι.range → (H → R) → T → R := fun c a x =>
    if (QuotientGroup.mk x : T ⧸ ι.range) = c then a (κ x) else 0
  have hext_mem : ∀ c a, a ∈ A → ext c a ∈ indOrder ι A := by
    intro c a ha
    rw [OrderApi.mem_indOrder]
    intro t
    have e : (fun h => ext c a (t * ι h)) =
        if (QuotientGroup.mk t : T ⧸ ι.range) = c then (fun h => a (κ t * h)) else 0 := by
      funext h
      simp only [ext, hmk, hκmul]
      split_ifs <;> rfl
    rw [e]
    split_ifs
    · exact translate_mem R H A hA a ha (κ t)
    · exact A.zero_mem
  have hdecomp : ∀ f : T → R, ∑ c, ext c (fun h => f (c.out * ι h)) = f := by
    intro f
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single (QuotientGroup.mk x)]
    · simp only [ext, ↓reduceIte, hκ]
    · intro c _ hc
      simp only [ext]
      rw [if_neg (fun h => hc h.symm)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  let extL : T ⧸ ι.range → (H → R) →ₗ[R] (T → R) := fun c =>
    { toFun := ext c
      map_add' := fun a b => by
        funext x
        simp only [ext, Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun r a => by
        funext x
        simp only [ext, Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
  let Φ : indOrder ι A →ₗ[R] (T ⧸ ι.range → A) :=
    { toFun := fun f c => ⟨fun h => (f : T → R) (c.out * ι h),
        (OrderApi.mem_indOrder ι A f).mp f.2 c.out⟩
      map_add' := fun f g => by
        funext c
        exact Subtype.ext rfl
      map_smul' := fun r f => by
        funext c
        exact Subtype.ext rfl }
  let Ψ : (T ⧸ ι.range → A) →ₗ[R] indOrder ι A :=
    { toFun := fun a => ⟨∑ c, extL c (a c),
        Subalgebra.sum_mem _ (fun c _ => hext_mem c (a c) (a c).2)⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp only [Pi.add_apply, Subalgebra.coe_add, map_add (f := _), Finset.sum_add_distrib]
      map_smul' := fun r a => by
        apply Subtype.ext
        simp only [Pi.smul_apply, Subalgebra.coe_smul, map_smul, Finset.smul_sum,
          RingHom.id_apply] }
  have hΨΦ : Ψ.comp Φ = LinearMap.id := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact hdecomp (f : T → R)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Module.Finite.of_surjective Ψ (fun f => ⟨Φ f, by
      rw [← LinearMap.comp_apply, hΨΦ, LinearMap.id_apply]⟩)
  · have : Module.Projective R (T ⧸ ι.range → A) :=
      Module.Projective.of_equiv
        (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : T ⧸ ι.range => A))
    exact Module.Projective.of_split Φ Ψ hΨΦ
  · obtain ⟨d, hd, hdf⟩ := hA.full
    refine ⟨d, hd, fun f => ?_⟩
    rw [OrderApi.mem_indOrder]
    intro t
    exact hdf _
  · intro f hf
    have hg : ∀ c c' : T ⧸ ι.range,
        (fun z : H × H => f (c.out * c'.out * ι (z.1 * z.2))) ∈ prodSpan A := fun c c' =>
      hA.comul _ ((OrderApi.mem_indOrder ι A f).mp hf (c.out * c'.out))
    have hlift : ∀ (c c' : T ⧸ ι.range) (G : H × H → R), G ∈ prodSpan A →
        (fun z : T × T => if (QuotientGroup.mk z.1 : T ⧸ ι.range) = c ∧
          (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' then G (κ z.1, κ z.2) else 0) ∈
          prodSpan (indOrder ι A) := by
      intro c c' G hG
      induction hG using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hg
        have e : (fun z : T × T => if (QuotientGroup.mk z.1 : T ⧸ ι.range) = c ∧
            (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' then a (κ z.1, κ z.2).1 * b (κ z.1, κ z.2).2
            else 0) = fun z => ext c a z.1 * ext c' b z.2 := by
          funext z
          by_cases h1 : (QuotientGroup.mk z.1 : T ⧸ ι.range) = c <;>
            by_cases h2 : (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' <;> simp [ext, h1, h2]
        rw [e]
        exact OrderApi.mul_mem_prodSpan (hext_mem c a ha) (hext_mem c' b hb)
      | zero =>
        convert (prodSpan (indOrder ι A)).zero_mem using 1
        funext z
        simp
      | add x y _ _ hx hy =>
        convert (prodSpan (indOrder ι A)).add_mem hx hy using 1
        funext z
        by_cases h1 : (QuotientGroup.mk z.1 : T ⧸ ι.range) = c <;>
          by_cases h2 : (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' <;>
          simp [h1, h2]
      | smul r x _ hx =>
        convert (prodSpan (indOrder ι A)).smul_mem r hx using 1
        funext z
        by_cases h1 : (QuotientGroup.mk z.1 : T ⧸ ι.range) = c <;>
          by_cases h2 : (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' <;>
          simp [h1, h2]
    have hsum : (fun z : T × T => f (z.1 * z.2)) = ∑ c : T ⧸ ι.range, ∑ c' : T ⧸ ι.range,
        (fun z : T × T => if (QuotientGroup.mk z.1 : T ⧸ ι.range) = c ∧
          (QuotientGroup.mk z.2 : T ⧸ ι.range) = c' then
          (fun w : H × H => f (c.out * c'.out * ι (w.1 * w.2))) (κ z.1, κ z.2) else 0) := by
      funext z
      rw [Finset.sum_apply, Finset.sum_eq_single (QuotientGroup.mk z.1)]
      · rw [Finset.sum_apply, Finset.sum_eq_single (QuotientGroup.mk z.2)]
        · simp only [and_self, ↓reduceIte]
          calc f (z.1 * z.2) = f ((QuotientGroup.mk z.1 : T ⧸ ι.range).out * ι (κ z.1) *
                ((QuotientGroup.mk z.2 : T ⧸ ι.range).out * ι (κ z.2))) := by rw [hκ, hκ]
            _ = _ := by rw [map_mul, mul_mul_mul_comm]
        · intro c' _ hc'
          rw [if_neg (fun h => hc' h.2.symm)]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro c _ hc
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro c' _
        rw [if_neg (fun h => hc h.1.symm)]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum]
    exact Submodule.sum_mem _ (fun c _ => Submodule.sum_mem _ (fun c' _ => hlift c c' _ (hg c c')))
  · intro f hf
    rw [OrderApi.mem_indOrder] at hf ⊢
    intro t
    have e : (fun h => f ((t * ι h)⁻¹)) = fun x => (fun h => f (t⁻¹ * ι h)) x⁻¹ := by
      funext h
      rw [mul_inv]
      simp only [map_inv]
    rw [e]
    exact hA.inv _ (hf t⁻¹)

theorem res_ind {R T : Type} [CommRing R] [CommGroup T] (H : Subgroup T) (A : Subalgebra R (H → R))
    (hA : IsHopfOrder A) : resOrder H.subtype (indOrder H.subtype A) = A := by
  classical
  apply le_antisymm
  · intro x hx
    obtain ⟨f, hf, rfl⟩ := Subalgebra.mem_map.mp hx
    have h1 := (OrderApi.mem_indOrder _ A f).mp hf 1
    convert h1 using 1
    funext h
    simp [GlobalTheory.CompanionTheory.Ar.BT.pullFun]
  · intro a ha
    let f : T → R := fun x => if hx : x ∈ H then a ⟨x, hx⟩ else 0
    have hf : f ∈ indOrder H.subtype A := by
      rw [OrderApi.mem_indOrder]
      intro t
      by_cases ht : t ∈ H
      · have e : (fun h : H => f (t * H.subtype h)) = fun h => a (⟨t, ht⟩ * h) := by
          funext h
          simp only [f, Subgroup.coe_subtype]
          rw [dite_eq_left (H.mul_mem ht h.2)]
          rfl
        rw [e]
        exact translate_mem R H A hA a ha ⟨t, ht⟩
      · have e : (fun h : H => f (t * H.subtype h)) = 0 := by
          funext h
          simp only [f, Subgroup.coe_subtype, Pi.zero_apply]
          rw [dite_eq_right]
          intro hm
          exact ht (by simpa using H.mul_mem hm (H.inv_mem h.2))
        rw [e]
        exact A.zero_mem
    exact Subalgebra.mem_map.mpr ⟨f, hf, by
      funext h
      simp [GlobalTheory.CompanionTheory.Ar.BT.pullFun, f]⟩

end PositivityTheory.HtPt.Twhopf
end

