module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0045

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpecAICPf
section
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.SpecAICPf

theorem aic_equiv {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A') (h : AIC A) : AIC A' := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _) (by rwa [natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have := congrArg e ha
  rw [eval_map, ← coe_eval₂RingHom, map_zero] at this
  rw [← this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [eval₂_eq_sum_range, eval_eq_sum_range, map_sum]

theorem card_roots_of_aic {A : Type} [CommRing A] [IsDomain A] (h : AIC A) :
    ∀ (n : ℕ) (p : A[X]), p.Monic → p.natDegree = n → Multiset.card p.roots = n := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    rw [eq_one_of_monic_natDegree_zero hp hn]; simp
  | succ n ih =>
    intro p hp hn
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    have e := mul_divByMonic_eq_iff_isRoot.2 ha
    have hq : (p /ₘ (X - C a)).Monic := Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [e]; exact hp)
    rw [← e, roots_mul (by rw [e]; exact hp.ne_zero), roots_X_sub_C, Multiset.card_add, ih _ hq hdeg]
    simp; omega

theorem aic_localization {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (M : Submonoid B)
    [IsLocalization M S] (h : AIC B) : AIC S := by
  classical
  intro p hp hd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M (Finset.image p.coeff (Finset.range (p.natDegree + 1)))
  set r : S := algebraMap B S b
  have hl : p.scaleRoots r ∈ lifts (algebraMap B S) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · obtain ⟨t, ht⟩ := hb (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      refine ⟨t * b ^ (p.natDegree - (i + 1)), ?_⟩
      rw [map_mul, ht, map_pow, Algebra.smul_def]
      simp only [r]
      have : p.natDegree - i = (p.natDegree - (i + 1)) + 1 := by omega
      rw [this, pow_succ]; ring
    · subst hi; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
    · rw [coeff_eq_zero_of_natDegree_lt hi]; exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff r).2 hp)
  obtain ⟨β, hβ⟩ := h q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)
  have hru : IsUnit r := IsLocalization.map_units S b
  refine ⟨algebraMap B S β * hru.unit⁻¹, ?_⟩
  have h1 := scaleRoots_eval₂_mul (p := p) (RingHom.id S) (algebraMap B S β * hru.unit⁻¹) r
  simp only [eval₂_id, RingHom.id_apply] at h1
  have h2 : r * (algebraMap B S β * hru.unit⁻¹) = algebraMap B S β := by
    rw [mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]
  rw [h2, ← hq, eval_map, eval₂_hom, hβ, map_zero] at h1
  exact (hru.pow _).mul_right_eq_zero.1 h1.symm

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

theorem roots_eq {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] (hK : Function.Injective (algebraMap R K)) (L : Subalgebra R K) (hL : AIC L)
    (p : R[X]) (hp : p.Monic) : (p.map (algebraMap R L)).roots.map L.val.toRingHom = (p.map (algebraMap R K)).roots ∧
      Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
  have hinj : Function.Injective (algebraMap R L) := by
    intro a b hab
    exact hK (congrArg Subtype.val hab)
  have hc : Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
    rw [card_roots_of_aic hL _ _ (hp.map _) rfl, natDegree_map_eq_of_injective hinj]
  refine ⟨?_, hc⟩
  rw [roots_map_of_injective_of_card_eq_natDegree (f := L.val.toRingHom) Subtype.val_injective
    (by rw [hc, natDegree_map_eq_of_injective hinj]), map_map]
  rfl

theorem aic_of_local {R : Type} [CommRing R] [IsDomain R]
    (h : ∀ v : MaximalSpectrum R, AIC (Localization.AtPrime v.asIdeal)) : AIC R := by
  classical
  intro p hp hd
  let K := FractionRing R
  let L : MaximalSpectrum R → Subalgebra R K := fun v =>
    Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors
  have hL : ∀ v, AIC (L v) := fun v =>
    aic_equiv (IsLocalization.algEquiv v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal) (L v)).toRingEquiv (h v)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  obtain ⟨e0, c0⟩ := roots_eq (IsFractionRing.injective R K) (L ⟨m, hm⟩) (hL _) p hp
  obtain ⟨x, hx⟩ : ∃ x, x ∈ (p.map (algebraMap R K)).roots := by
    rw [← e0]
    apply Multiset.exists_mem_of_ne_zero
    intro h0
    rw [Multiset.map_eq_zero] at h0
    rw [h0] at c0; simp at c0; omega
  have hmem : x ∈ (⊥ : Subalgebra R K) := by
    rw [← MaximalSpectrum.iInf_localization_eq_bot R K, Algebra.mem_iInf]
    intro v
    rw [← (roots_eq (IsFractionRing.injective R K) (L v) (hL v) p hp).1] at hx
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
    exact y.2
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.1 hmem
  refine ⟨a, ?_⟩
  have hr := (mem_roots (hp.map _).ne_zero).1 hx
  rw [IsRoot, eval_map, eval₂_hom] at hr
  exact (IsFractionRing.injective R K) (by rw [hr, map_zero])

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

open CategoryTheory AlgebraicGeometry

theorem stalk_aic (B : CommRingCat.{0}) (hA : AIC B) (x : Spec B) : AIC ((Spec B).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  let _ : Algebra B ((Spec B).presheaf.stalk x) := StructureSheaf.stalkAlgebra B x
  have : IsLocalization.AtPrime ((Spec B).presheaf.stalk x) x.asIdeal := StructureSheaf.IsLocalization.to_stalk B x
  exact aic_localization x.asIdeal.primeCompl hA

theorem SpecAIC_of : LateralTheory.E.FibreEqvPf.SpecAIC := by
  intro B hB hA
  refine ⟨inferInstance, ?_⟩
  intro U hU hne
  haveI : Nonempty U := hne.to_subtype
  apply aic_of_local
  intro v
  let y : PrimeSpectrum Γ(Spec B, U) := ⟨v.asIdeal, v.isMaximal.isPrime⟩
  have hy : hU.fromSpec y ∈ U := by
    show hU.fromSpec y ∈ (U : Set (Spec B))
    rw [← hU.range_fromSpec]; exact ⟨y, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk (Spec B).presheaf ⟨hU.fromSpec y, hy⟩
  have hloc : IsLocalization.AtPrime ((Spec B).presheaf.stalk (hU.fromSpec y)) y.asIdeal := hU.isLocalization_stalk' y hy
  have hst := stalk_aic B hA (hU.fromSpec y)
  exact aic_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl ((Spec B).presheaf.stalk (hU.fromSpec y))
    (Localization.AtPrime v.asIdeal)).toRingEquiv hst

end LateralTheory.E.SpecAICPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TowerFinPf
section
noncomputable section
open CategoryTheory Limits Category Pretriangulated GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf

namespace LateralTheory.E.TowerFinPf

abbrev Q (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

section RelYLemmas
variable (R : Type) [CommRing R] (F : Shv R) (n : ℤ)

theorem relY_of_iso {A B A' B' : HomotopyCategory (Shv R) (ComplexShape.up ℤ)} (g : A ⟶ B) (g' : A' ⟶ B')
    (e₁ : A' ≅ A) (e₂ : B' ≅ B) (w : g' ≫ e₂.hom = e₁.hom ≫ g) (h : Tri.RelY (Yres R F) n g) :
    Tri.RelY (Yres R F) n g' := by
  have w' : g ≫ e₂.inv = e₁.inv ≫ g' := by
    rw [Iso.eq_inv_comp, ← assoc, ← w, assoc, Iso.hom_inv_id, comp_id]
  refine ⟨fun y => ?_, fun x₁ x₂ hx => ?_⟩
  · obtain ⟨x, hx⟩ := h.1 (e₁.inv ≫ y)
    refine ⟨e₂.hom ≫ x, ?_⟩
    simp only at hx ⊢
    rw [← assoc, w, assoc, hx, Iso.hom_inv_id_assoc]
  · simp only at hx
    have : e₂.inv ≫ x₁ = e₂.inv ≫ x₂ := h.2 (by
      simp only
      rw [← assoc, w', assoc, hx, ← assoc, ← w', assoc])
    simpa using congrArg (e₂.hom ≫ ·) this

theorem relY_zero {A B : HomotopyCategory (Shv R) (ComplexShape.up ℤ)} (g : A ⟶ B) (hA : IsZero A) (hB : IsZero B) :
    Tri.RelY (Yres R F) n g :=
  ⟨fun y => ⟨0, hA.eq_of_src _ _⟩, fun _ _ _ => hB.eq_of_src _ _⟩

theorem isZero_cx {K : Cx R} (h : ∀ i, IsZero (K.X i)) : IsZero K := by
  rw [IsZero.iff_id_eq_zero]
  ext i : 1
  exact (h i).eq_of_src _ _

theorem relK_zero {K L : Cx R} (f : K ⟶ L) (hK : ∀ i, IsZero (K.X i)) (hL : ∀ i, IsZero (L.X i)) :
    RelK R F n f :=
  (relK_iff R f F n).2 (relY_zero R F n _ ((Q R).map_isZero (isZero_cx R hK)) ((Q R).map_isZero (isZero_cx R hL)))

theorem relK_piece_zero {K L : Cx R} (f : K ⟶ L) (p : ℕ) (hK : IsZero (K.X (-(p : ℤ)))) (hL : IsZero (L.X (-(p : ℤ)))) :
    RelK R F n (pieceC R f p) :=
  (relK_iff R _ F n).2 (relY_zero R F n _
    ((Q R).map_isZero ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).map_isZero hK))
    ((Q R).map_isZero ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).map_isZero hL)))

theorem relK_piece_iso {K L K' L' : Cx R} (f : K ⟶ L) (g : K' ⟶ L') (p : ℕ)
    (α : K'.X (-(p : ℤ)) ≅ K.X (-(p : ℤ))) (β : L'.X (-(p : ℤ)) ≅ L.X (-(p : ℤ)))
    (w : g.f (-(p : ℤ)) ≫ β.hom = α.hom ≫ f.f (-(p : ℤ))) (h : RelK R F n (pieceC R f p)) :
    RelK R F n (pieceC R g p) := by
  rw [relK_iff] at h ⊢
  refine relY_of_iso R F n _ _ ((Q R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).mapIso α))
    ((Q R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) _).mapIso β)) ?_ h
  simp only [Functor.mapIso_hom, pieceC, ← Functor.map_comp, w]

end RelYLemmas

theorem inv_nat {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ : C} (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂) [IsIso g₁] [IsIso g₂]
    (t₂ : X₁ ⟶ X₂) (t₃ : Y₁ ⟶ Y₂) (h : g₁ ≫ t₃ = t₂ ≫ g₂) : t₃ ≫ inv g₂ = inv g₁ ≫ t₂ := by
  rw [IsIso.comp_inv_eq, assoc, IsIso.eq_inv_comp, h]

theorem aux {C : Type*} [Category C] {A₃ A₂ B₂ B₁ A₃' A₂' B₂' B₁' : C} (s₁ : A₃ ⟶ A₂) (d₁ : A₂ ⟶ B₂)
    (r₁ : B₂ ⟶ B₁) (t₁ : B₁ ⟶ B₁') (t₃ : A₃ ⟶ A₃') (s₂ : A₃' ⟶ A₂') (d₂ : A₂' ⟶ B₂') (r₂ : B₂' ⟶ B₁')
    (ta : A₂ ⟶ A₂') (tb : B₂ ⟶ B₂') (hs : t₃ ≫ s₂ = s₁ ≫ ta) (hc : ta ≫ d₂ = d₁ ≫ tb) (hr : tb ≫ r₂ = r₁ ≫ t₁) :
    (s₁ ≫ d₁ ≫ r₁) ≫ t₁ = t₃ ≫ s₂ ≫ d₂ ≫ r₂ := by
  rw [reassoc_of% hs, reassoc_of% hc, hr]; simp only [assoc]

theorem hom_nat {C : Type*} [Category C] [Preadditive C] {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
    (σ₁ : ∀ n, (S₁.map (HomologicalComplex.eval C _ n)).Splitting)
    (σ₂ : ∀ n, (S₂.map (HomologicalComplex.eval C _ n)).Splitting)
    (hs : ∀ n, φ.τ₃.f n ≫ (σ₂ n).s = (σ₁ n).s ≫ φ.τ₂.f n)
    (hr : ∀ n, φ.τ₂.f n ≫ (σ₂ n).r = (σ₁ n).r ≫ φ.τ₁.f n) :
    CochainComplex.homOfDegreewiseSplit S₁ σ₁ ≫ (CategoryTheory.shiftFunctor _ (1 : ℤ)).map φ.τ₁ =
      φ.τ₃ ≫ CochainComplex.homOfDegreewiseSplit S₂ σ₂ := by
  ext n
  simp [CochainComplex.cocycleOfDegreewiseSplit, CochainComplex.shiftFunctor_map_f']
  simpa only [assoc] using aux _ _ _ _ _ _ _ _ _ _ (hs n) (φ.τ₂.comm n (n + 1)) (hr (n + 1))

section Step
variable {R : Type} [CommRing R]

def qK (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) :
    K ⟶ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).obj (K.X a) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun j hj => (hK j (by simp at hj; omega)).eq_of_src _ _)

theorem qK_iso (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) : IsIso ((qK K a hK).f a) := by
  rw [qK, HomologicalComplex.mkHomToSingle_f]; infer_instance

theorem qK_zero (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) (hm : m ≠ a) : (qK K a hK).f m = 0 :=
  (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm).eq_of_tgt _ _

def lim (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) :=
  KernelFork.mapIsLimit _ (kernelIsKernel (qK K a hK)) (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) m)

theorem ι_iso (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) (hm : m ≠ a) :
    IsIso ((kernel.ι (qK K a hK)).f m) :=
  isIso_limit_cone_parallelPair_of_eq (by exact qK_zero K a hK m hm) (lim K a hK m)

theorem ker_zero (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) :
    IsZero ((kernel (qK K a hK)).X a) := by
  have := qK_iso K a hK
  rw [IsZero.iff_id_eq_zero]
  refine Fork.IsLimit.hom_ext (lim K a hK a) ?_
  have h0 : (kernel.ι (qK K a hK)).f a = 0 := by
    rw [← cancel_mono ((qK K a hK).f a), ← HomologicalComplex.comp_f, kernel.condition]; simp
  change 𝟙 _ ≫ (kernel.ι (qK K a hK)).f a = 0 ≫ (kernel.ι (qK K a hK)).f a
  rw [h0, comp_zero, zero_comp]

theorem inv_nat' {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ : C} (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂) [IsIso g₁] [IsIso g₂]
    (t₂ : X₁ ⟶ X₂) (t₃ : Y₁ ⟶ Y₂) (h : g₁ ≫ t₃ = t₂ ≫ g₂) : t₃ ≫ inv g₂ = inv g₁ ≫ t₂ := inv_nat g₁ g₂ t₂ t₃ h

abbrev MainNotions (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) : ShortComplex (Cx R) :=
  ShortComplex.mk (kernel.ι (qK K a hK)) (qK K a hK) (kernel.condition _)

def spl (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (m : ℤ) :
    ((MainNotions K a hK).map (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) m)).Splitting :=
  if h : m = a then
    ShortComplex.Splitting.ofIsZeroOfIsIso _ (by subst h; exact ker_zero K m hK) (by subst h; exact qK_iso K m hK)
  else ShortComplex.Splitting.ofIsIsoOfIsZero _ (ι_iso K a hK m h) (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (K.X a) m h)

theorem dist (K : Cx R) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) :
    CochainComplex.trianglehOfDegreewiseSplit (MainNotions K a hK) (spl K a hK) ∈ distTriang _ :=
  (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).2 ⟨_, _, ⟨Iso.refl _⟩⟩

variable {K L : Cx R} (f : K ⟶ L) (a : ℤ) (hK : ∀ i, i < a → IsZero (K.X i)) (hL : ∀ i, i < a → IsZero (L.X i))

abbrev pc : (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).obj (K.X a) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).obj (L.X a) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) a).map (f.f a)

theorem hqf : qK K a hK ≫ pc f a = f ≫ qK L a hL := by
  apply HomologicalComplex.to_single_hom_ext
  simp [qK, pc, HomologicalComplex.single_map_f_self]

def sf : kernel (qK K a hK) ⟶ kernel (qK L a hL) := kernel.map _ _ f (pc f a) (hqf f a hK hL)

theorem hι : sf f a hK hL ≫ kernel.ι (qK L a hL) = kernel.ι (qK K a hK) ≫ f := by
  simp [sf]

def phiS : MainNotions K a hK ⟶ MainNotions L a hL where
  τ₁ := sf f a hK hL
  τ₂ := f
  τ₃ := pc f a
  comm₁₂ := hι f a hK hL
  comm₂₃ := (hqf f a hK hL).symm

theorem hs (m : ℤ) : (phiS f a hK hL).τ₃.f m ≫ (spl L a hL m).s = (spl K a hK m).s ≫ (phiS f a hK hL).τ₂.f m := by
  unfold spl
  split_ifs with h
  · subst h
    exact @inv_nat' _ _ _ _ _ _ _ _ (qK_iso K m hK) (qK_iso L m hL) _ _ (HomologicalComplex.congr_hom (phiS f m hK hL).comm₂₃ m).symm
  · simp only [ShortComplex.Splitting.ofIsIsoOfIsZero]
    erw [comp_zero, zero_comp]

theorem hr (m : ℤ) : (phiS f a hK hL).τ₂.f m ≫ (spl L a hL m).r = (spl K a hK m).r ≫ (phiS f a hK hL).τ₁.f m := by
  unfold spl
  split_ifs with h
  · simp only [ShortComplex.Splitting.ofIsZeroOfIsIso]
    erw [comp_zero, zero_comp]
  · exact @inv_nat' _ _ _ _ _ _ _ _ (ι_iso K a hK m h) (ι_iso L a hL m h) _ _ (HomologicalComplex.congr_hom (phiS f a hK hL).comm₁₂ m).symm

def triMap : CochainComplex.triangleOfDegreewiseSplit (MainNotions K a hK) (spl K a hK) ⟶
    CochainComplex.triangleOfDegreewiseSplit (MainNotions L a hL) (spl L a hL) :=
  Triangle.homMk _ _ (sf f a hK hL) f (pc f a) (hι f a hK hL).symm (hqf f a hK hL)
    (hom_nat (phiS f a hK hL) _ _ (hs f a hK hL) (hr f a hK hL))

end Step

section Main
variable (R : Type) [CommRing R] (F : Shv R) (n : ℤ)

theorem claim : ∀ (N : ℕ) {K L : Cx R} (f : K ⟶ L),
    (∀ i : ℤ, (0 < i ∨ i < -(N : ℤ) + 1) → IsZero (K.X i) ∧ IsZero (L.X i)) →
    (∀ p : ℕ, RelK R F n (pieceC R f p)) → RelK R F n f
  | 0, K, L, f, hz, _ => relK_zero R F n f (fun i => (hz i (by omega)).1) (fun i => (hz i (by omega)).2)
  | N + 1, K, L, f, hz, hp => by
    have hK : ∀ i, i < -(N : ℤ) → IsZero (K.X i) := fun i hi => (hz i (by push_cast; omega)).1
    have hL : ∀ i, i < -(N : ℤ) → IsZero (L.X i) := fun i hi => (hz i (by push_cast; omega)).2
    have ih := claim N (sf f (-(N : ℤ)) hK hL) (fun i hi => ?_) (fun p => ?_)
    · have h3 := hp N
      rw [relK_iff] at ih h3 ⊢
      exact Tri.relY_mid _ _ (dist K _ hK) (dist L _ hL) ((Q R).mapTriangle.map (triMap f _ hK hL))
        (Yres R F) (yresIso R F) n ih h3
    · by_cases hia : i = -(N : ℤ)
      · subst hia; exact ⟨ker_zero K _ hK, ker_zero L _ hL⟩
      · have h1 := ι_iso K _ hK i hia
        have h2 := ι_iso L _ hL i hia
        have hz' := hz i (by push_cast; omega)
        exact ⟨hz'.1.of_iso (asIso ((kernel.ι (qK K _ hK)).f i)), hz'.2.of_iso (asIso ((kernel.ι (qK L _ hL)).f i))⟩
    · by_cases hpa : -(p : ℤ) = -(N : ℤ)
      · exact relK_piece_zero R F n _ p (by rw [hpa]; exact ker_zero K _ hK) (by rw [hpa]; exact ker_zero L _ hL)
      · exact relK_piece_iso R F n f _ p (@asIso _ _ _ _ ((kernel.ι (qK K _ hK)).f _) (ι_iso K _ hK _ hpa))
          (@asIso _ _ _ _ ((kernel.ι (qK L _ hL)).f _) (ι_iso L _ hL _ hpa))
          (HomologicalComplex.congr_hom (hι f _ hK hL) _) (hp p)

end Main

end LateralTheory.E.TowerFinPf

theorem LateralTheory.E.FiltPf.TowerFin_of : LateralTheory.E.FiltPf.TowerFin := by
  intro R _ F K L f n P hz hp
  exact LateralTheory.E.TowerFinPf.claim R F n (P + 1) f (fun i hi => hz i (by push_cast at hi; omega)) hp
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TruncPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncPf

def TruncBij : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K K' : Cx R} (g : K ⟶ K') (n : ℤ),
  (∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p)) → ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R g F m)

def TruncData : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  ∃ (P : ℕ) (K' L' : Cx R) (f' : K' ⟶ L') (g : K ⟶ K') (h : L ⟶ L'),
    (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K'.X i) ∧ IsZero (L'.X i)) ∧ g ≫ f' = f ≫ h ∧
    (∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p) ∧ IsIso (h.f p)) ∧
    (∀ p : ℤ, p < -(n + 1) → IsZero (K'.X p) ∧ IsZero (L'.X p))

variable (R : Type) [CommRing R] (F : Shv R)

theorem toHom_inj {K : Cx R} (m : ℤ) {x y : HK R K F m}
    (h : CohomologyClass.toHom x = CohomologyClass.toHom y) : x = y := by
  apply CohomologyClass.homAddEquiv.injective
  simpa only [CohomologyClass.homAddEquiv_apply] using h

theorem pull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (m : ℤ) (x : HK R M F m) :
    HK.pull R (f ≫ g) F m x = HK.pull R f F m (HK.pull R g F m x) := by
  apply toHom_inj
  simp only [LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom, Functor.map_comp, Category.assoc]

theorem pull_id {K : Cx R} (m : ℤ) (x : HK R K F m) : HK.pull R (𝟙 K) F m x = x := by
  apply toHom_inj
  rw [LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom]
  erw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

theorem pull_bij_of_iso {K L : Cx R} (f : K ⟶ L) [IsIso f] (m : ℤ) : Function.Bijective (HK.pull R f F m) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨HK.pull R (inv f) F m y, ?_⟩⟩
  · have := congrArg (HK.pull R (inv f) F m) hxy
    simpa only [← pull_comp, IsIso.inv_hom_id, pull_id] using this
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem subsingleton_of_isZero {K : Cx R} (hK : IsZero K) (m : ℤ) : Subsingleton (HK R K F m) := by
  constructor
  intro x y
  apply toHom_inj
  exact (Functor.map_isZero (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)) hK).eq_of_src _ _

theorem relK_of_isZero {K L : Cx R} (f : K ⟶ L) (n : ℤ) (hK : IsZero K) (hL : IsZero L) : RelK R F n f :=
  ⟨fun m _ _ => ⟨0, (subsingleton_of_isZero R F hK m).elim _ _⟩,
    fun _ _ _ => (subsingleton_of_isZero R F hL n).elim _ _⟩

theorem relK_of_square {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L') (g : K ⟶ K') (h : L ⟶ L')
    (w : g ≫ f' = f ≫ h) (n : ℤ)
    (hg : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R g F m))
    (hh : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R h F m))
    (hf' : RelK R F n f') : RelK R F n f := by
  have key : ∀ (m : ℤ) (z : HK R L' F m),
      HK.pull R f F m (HK.pull R h F m z) = HK.pull R g F m (HK.pull R f' F m z) := by
    intro m z
    rw [← pull_comp, ← pull_comp, w]
  refine ⟨fun m hm y => ?_, fun x1 x2 hx => ?_⟩
  · obtain ⟨y', rfl⟩ := (hg m (by omega)).2 y
    obtain ⟨z, rfl⟩ := hf'.1 m hm y'
    exact ⟨_, key m z⟩
  · obtain ⟨w1, rfl⟩ := (hh n le_rfl).2 x1
    obtain ⟨w2, rfl⟩ := (hh n le_rfl).2 x2
    rw [key, key] at hx
    rw [hf'.2 ((hg n le_rfl).1 hx)]

theorem piece_transfer {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L') (g : K ⟶ K') (h : L ⟶ L')
    (w : g ≫ f' = f ≫ h) (n : ℤ) (p : ℕ) (hg : IsIso (g.f (-(p : ℤ)))) (hh : IsIso (h.f (-(p : ℤ))))
    (hp : RelK R F n (pieceC R f p)) : RelK R F n (pieceC R f' p) := by
  refine relK_of_square R F (pieceC R f' p) (pieceC R f p)
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (inv (g.f _)))
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (inv (h.f _))) ?_ n
    (fun m _ => pull_bij_of_iso R F _ m) (fun m _ => pull_bij_of_iso R F _ m) hp
  simp only [pieceC, ← Functor.map_comp]
  congr 1
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  have := congrArg (fun φ => HomologicalComplex.Hom.f φ (-(p : ℤ))) w
  simp only [HomologicalComplex.comp_f] at this
  exact this.symm

end LateralTheory.E.TruncPf

open LateralTheory.E.TruncPf in
theorem LateralTheory.E.TruncPf.Trunc_of (hB : TruncBij) (hD : TruncData) : LateralTheory.E.FiltPf.Trunc := by
  intro R _ F K L f n hz
  obtain ⟨P, K', L', f', g, h, hb, w, hiso, hzero⟩ := hD R f n hz
  refine ⟨P, K', L', f', hb, fun hp p => ?_, relK_of_square R F f f' g h w n
    (hB R F g n fun q hq => (hiso q hq).1) (hB R F h n fun q hq => (hiso q hq).2)⟩
  by_cases hq : -(n + 1) ≤ -(p : ℤ)
  · exact piece_transfer R F f f' g h w n p (hiso _ hq).1 (hiso _ hq).2 (hp p)
  · exact relK_of_isZero R F _ n
      (Functor.map_isZero _ (hzero _ (by omega)).1) (Functor.map_isZero _ (hzero _ (by omega)).2)
end
end

