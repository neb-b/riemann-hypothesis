module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueZpowMulAppLE

@[expose] public section

universe u v

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.DvrModel

open PrimeSection

variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {K : Type u} [Field K] [Algebra V K] [IsFractionRing V K] {ϖ : V}
  {H : Scheme.{u}} {f : H ⟶ Spec (.of V)}
  {HK : Scheme.{u}} {j : HK ⟶ H} {fK : HK ⟶ Spec (.of K)}
  {Hs : Scheme.{u}} {i : Hs ⟶ H} {fs : Hs ⟶ Spec (.of (ResidueField V))}


variable (K) in
theorem isLocalization_away (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ) (nonZeroDivisors V)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero) fun a ha ↦ ?_).2 inferInstance
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero ha) hϖ
  exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩


variable (f) in
theorem notMem_basicOpen_iff (hϖ : Irreducible ϖ) (x : H) :
    x ∉ H.basicOpen (f.appTop ((Scheme.ΓSpecIso (.of V)).inv ϖ)) ↔ f x = closedPoint V := by
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  change ¬ ϖ ∉ (f x).asIdeal ↔ _
  rw [not_not]
  constructor
  · intro h
    refine PrimeSpectrum.ext ((maximalIdeal.isMaximal V).eq_of_le (f x).2.ne_top ?_).symm
    rwa [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
  · intro h
    rw [h]
    exact hϖ.not_isUnit

theorem isOpenImmersion_generic
    (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K)))) :
    IsOpenImmersion j := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isLocalization_away (K := K) hϖ
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hK.flip
    (IsOpenImmersion.of_isLocalization ϖ)

theorem opensRange_generic (hϖ : Irreducible ϖ) [IsOpenImmersion j]
    (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K)))) :
    j.opensRange = H.basicOpen (f.appTop ((Scheme.ΓSpecIso (.of V)).inv ϖ)) := by
  have := isLocalization_away (K := K) hϖ
  have hr := PrimeSpectrum.localization_away_comap_range K ϖ
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨y, rfl⟩
    change f (j y) ∈ (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum V))
    rw [← hr, ← Scheme.Hom.comp_apply, hK.w]
    exact ⟨fK y, rfl⟩
  · obtain ⟨z, hz⟩ : f x ∈ Set.range (PrimeSpectrum.comap (algebraMap V K)) := hr.ge hx
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hK x z hz.symm
    exact ⟨y, hy⟩

theorem mem_range_special
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) (x : H) :
    x ∈ Set.range i ↔ f x = closedPoint V := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, hs.w]
    exact PrimeSpectrum.comap_residue V (fs y)
  · intro h
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hs x (closedPoint _)
      (h.trans (PrimeSpectrum.comap_residue V _).symm)
    exact ⟨y, hy⟩


variable (f) in
omit [IsDiscreteValuationRing V] in
theorem res_mem_nonZeroDivisors [Flat f] {c : V} (hc : c ≠ 0) {U : H.Opens}
    (hU : IsAffineOpen U) :
    H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.appTop ((Scheme.ΓSpecIso (.of V)).inv c)) ∈ nonZeroDivisors Γ(H, U) := by
  have hf := f.flat_appLE (isAffineOpen_top _) hU le_top
  let := (f.appLE ⊤ U le_top).hom.toAlgebra
  have hc' : (Scheme.ΓSpecIso (.of V)).inv c ≠ 0 :=
    (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso _).1).2 hc
  have : Module.Flat Γ(Spec (.of V), ⊤) Γ(H, U) := hf
  have := IsSMulRegular.of_flat (S := Γ(H, U)) (IsSMulRegular.of_ne_zero hc')
  exact mem_nonZeroDivisors_iff_left.2 fun z hz ↦ this (hz.trans (smul_zero _).symm)

theorem isIntegral [Flat f] [IsIntegral HK]
    (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K)))) : IsIntegral H := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isOpenImmersion_generic hK
  exact isIntegral_of_basicOpen (fun U hU ↦ res_mem_nonZeroDivisors f hϖ.ne_zero hU) j
    (opensRange_generic hϖ hK)

theorem notMem_basicOpen_iff_specializes (hϖ : Irreducible ϖ) [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) (x : H) :
    x ∉ H.basicOpen (f.appTop ((Scheme.ΓSpecIso (.of V)).inv ϖ)) ↔ i (genericPoint Hs) ⤳ x := by
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := (mem_range_special hs x).2 ((notMem_basicOpen_iff f hϖ x).1 h)
    exact ((genericPoint_spec Hs).specializes trivial).map i.continuous
  · intro h hx
    exact (notMem_basicOpen_iff f hϖ _).2 ((mem_range_special hs _).1 ⟨_, rfl⟩)
      (h.mem_open (H.basicOpen _).isOpen hx)

theorem prime_res (hϖ : Irreducible ϖ) [Flat f] [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) {U : H.Opens}
    (hU : IsAffineOpen U) {x : H} (hx : x ∈ U) (hfx : f x = closedPoint V) :
    Prime (H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.appTop ((Scheme.ΓSpecIso (.of V)).inv ϖ))) := by
  obtain ⟨y, rfl⟩ := (mem_range_special hs x).2 hfx
  have : Nonempty (i ⁻¹ᵁ U) := ⟨⟨y, hx⟩⟩
  have : Nonempty U := ⟨⟨_, hx⟩⟩
  rw [← Ideal.span_singleton_prime
      (nonZeroDivisors.ne_zero (res_mem_nonZeroDivisors f hϖ.ne_zero hU)),
    ← ker_app_eq_span (β := CommRingCat.ofHom (residue V)) residue_surjective
      (ker_residue.trans hϖ.maximalIdeal_eq) hs hU]
  exact RingHom.ker_isPrime _

theorem prime_res_generic (hϖ : Irreducible ϖ) [Flat f] [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) (U : H.Opens)
    (hU : IsAffineOpen U) (h : i (genericPoint Hs) ∈ U) :
    Prime (H.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.appTop ((Scheme.ΓSpecIso (.of V)).inv ϖ))) :=
  prime_res hϖ hs hU h ((mem_range_special hs _).1 ⟨_, rfl⟩)

variable (f) in
theorem isLocallyNoetherian [LocallyOfFiniteType f] : IsLocallyNoetherian H :=
  LocallyOfFiniteType.isLocallyNoetherian f

theorem isDiscreteValuationRing_stalk_generic (hϖ : Irreducible ϖ) [Flat f]
    [LocallyOfFiniteType f] [IsIntegral H] [IsIntegral Hs]
    (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V)))) :
    IsDiscreteValuationRing (H.presheaf.stalk (i (genericPoint Hs))) ∧
      Irreducible (H.presheaf.germ ⊤ (i (genericPoint Hs)) trivial (f.appTop ((Scheme.ΓSpecIso (.of V)).inv ϖ))) :=
  haveI := isLocallyNoetherian f
  isDiscreteValuationRing_stalk (notMem_basicOpen_iff_specializes hϖ hs) (prime_res_generic hϖ hs)


omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] in
theorem appTop_cst (hw : j ≫ f = fK ≫ Spec.map (CommRingCat.ofHom (algebraMap V K))) (c : V) :
    j.appTop (f.appTop ((Scheme.ΓSpecIso (.of V)).inv c)) = fK.appTop ((Scheme.ΓSpecIso (.of K)).inv (algebraMap V K c)) := by
  have h₁ := congrArg (fun φ : HK ⟶ Spec (.of V) ↦ φ.appTop ((Scheme.ΓSpecIso (.of V)).inv c)) hw
  have h₂ := congrArg (fun φ : CommRingCat.of V ⟶ Γ(Spec (.of K), ⊤) ↦ φ c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V K)))
  exact h₁.trans (congrArg fK.appTop h₂.symm)

theorem pull_U {X Y : Scheme.{u}} (L : LB X) (φ : Y ⟶ X) (a : PUnit → L.ι) :
    (L.pull φ).U a = φ ⁻¹ᵁ L.U (a ⟨⟩) :=
  le_antisymm (LB.wchart_le L (fun _ ↦ φ) a ⟨⟩) fun _ hy ↦ Set.mem_iInter.2 fun _ ↦ hy

theorem wchart_comp {X Y Z : Scheme.{u}} (L : LB X) {κ : Type u} [Fintype κ] (h : Z ⟶ Y)
    (φ : κ → (Y ⟶ X)) (a : κ → L.ι) :
    LB.wchart L (fun k ↦ h ≫ φ k) a = h ⁻¹ᵁ LB.wchart L φ a :=
  le_antisymm (LB.wchart_comp_le L h φ a) fun _ hy ↦
    Set.mem_iInter.2 fun k ↦ Set.mem_iInter.1 hy k

theorem coe_pull_g {X Y : Scheme.{u}} (L : LB X) (φ : Y ⟶ X) (a b : PUnit → L.ι) :
    ((L.pull φ).g a b : Γ(Y, (L.pull φ).U a ⊓ (L.pull φ).U b)) =
      φ.appLE (L.U (a ⟨⟩) ⊓ L.U (b ⟨⟩)) _ (inf_le_inf (pull_U L φ a).le (pull_U L φ b).le)
        (L.g (a ⟨⟩) (b ⟨⟩) : Γ(X, L.U (a ⟨⟩) ⊓ L.U (b ⟨⟩))) :=
  congrArg Units.val (LB.lcg_pull L φ a b)

theorem coe_res_pullGen {X Y Z : Scheme.{u}} (L : LB X) {κ : Type u} [Fintype κ]
    (φ : κ → (Y ⟶ X)) (ε : κ → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (a : κ → L.ι)
    {A : Z.Opens} (hA : A ≤ LB.wchart L (fun k ↦ h ≫ φ k) a) :
    (res hA (LB.ts (LB.pullGen L φ ε c h) a) : Γ(Z, A)ˣ) =
      h.appLE (LB.wchart L φ a) A (hA.trans (LB.wchart_comp_le L h φ a))
        (LB.ts c a : Γ(Y, LB.wchart L φ a)ˣ) :=
  res_appLE h (LB.wchart_comp_le L h φ a) hA _

section Main

variable [Flat f] [LocallyOfFiniteType f] [IsIntegral HK] [IsIntegral Hs]
  (hK : IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
  (hs : IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V))))

include hK hs

theorem existsUnique_isUnit_appLE_eq {ι : Type v} {U : ι → H.Opens}
    {g : ∀ a b, Γ(H, U a ⊓ U b)} {W : ι → HK.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
    (hU : ∀ x : H, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b)) {r : ∀ a, Γ(HK, W a)}
    (hr : ∀ a b, HK.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        HK.presheaf.map (homOfLE inf_le_right).op (r b))
    (hru : ∀ a, IsUnit (r a)) {e : Spec (.of V) ⟶ H} (he : e ≫ f = 𝟙 _)
    {eK : Spec (.of K) ⟶ HK} (heK : eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e)
    {a₀ : ι} {A : (Spec (.of V)).Opens} (hyA : closedPoint V ∈ A) (hA : A ≤ e ⁻¹ᵁ U a₀)
    {A' : (Spec (.of K)).Opens} (hA' : A' = Spec.map (CommRingCat.ofHom (algebraMap V K)) ⁻¹ᵁ A)
    (hA'' : A' ≤ eK ⁻¹ᵁ W a₀) {u : Γ(Spec (.of V), A)} (hu : IsUnit u)
    (hur : (Spec.map (CommRingCat.ofHom (algebraMap V K))).appLE A A' hA'.le u =
      eK.appLE (W a₀) A' hA'' (r a₀)) :
    ∃! s : ∀ a, Γ(H, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, H.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * H.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, j.appLE (U a) (W a) (hW a).le (s a) = r a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isOpenImmersion_generic hK
  have := isIntegral hK
  have := isLocallyNoetherian f
  have := isLocalization_away (K := K) hϖ
  have := IsOpenImmersion.of_isLocalization (S := K) ϖ
  refine existsUnique_of_exists_of_unique
    (exists_isUnit_appLE_eq (notMem_basicOpen_iff_specializes hϖ hs)
      (prime_res_generic hϖ hs) (opensRange_generic hϖ hK) hW hU hg hr hru e
      (Spec.map (CommRingCat.ofHom (algebraMap V K))) eK heK ?_ hyA hA hA' hA'' hu hur)
    fun s s' h h' ↦ funext fun a ↦ appLE_injective j (hW a) ((h.2.2 a).trans (h'.2.2 a).symm)
  rw [notMem_basicOpen_iff f hϖ, ← Scheme.Hom.comp_apply, he]
  rfl

theorem existsUnique_gen {e : Spec (.of V) ⟶ H} (he : e ≫ f = 𝟙 _)
    {eK : Spec (.of K) ⟶ HK} (heK : eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e)
    {L : LB H} (hL : L.IsLB) (r : LB.Gen (L.pull j)) (hr : r.IsGen) (ρ : LB.Gen (L.pull e))
    (hρ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ r eK)
      (LB.pullGen L _ _ ρ (Spec.map (CommRingCat.ofHom (algebraMap V K))))) :
    ∃! r' : LB.Gen L, r'.IsGen ∧ LB.genPull L r' j = r := by
  obtain ⟨a₀, h₀⟩ := LB.mem_of_cover hL (e (closedPoint V))
  have hc := congrArg Units.val
    (hρ (fun _ ↦ a₀) (fun _ ↦ a₀) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) fun _ _ _ ↦ rfl)
  obtain ⟨s, ⟨hsu, hsc, hsr⟩, huniq⟩ := existsUnique_isUnit_appLE_eq hK hs
    (U := L.U) (g := fun a b ↦ L.g a b) (W := fun a ↦ (L.pull j).U fun _ ↦ a)
    (fun a ↦ pull_U L j _) (LB.mem_of_cover hL) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ r.s fun _ ↦ a)
    (fun a b ↦ by
      rw [← coe_pull_g L j (fun _ ↦ a) (fun _ ↦ b)]
      exact congrArg Units.val (hr _ _))
    (fun a ↦ Units.isUnit _) he heK (a₀ := a₀) (A := (L.pull e).U fun _ ↦ a₀)
    ((pull_U L e _).ge h₀) (pull_U L e _).le
    (A' := LB.wchart L (fun _ : PUnit ↦ eK ≫ j) (fun _ ↦ a₀) ⊓
      LB.wchart L (fun _ : PUnit ↦ Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e) fun _ ↦ a₀)
    (by rw [heK, inf_idem]; exact wchart_comp L _ (fun _ ↦ e) _)
    (inf_le_left.trans (wchart_comp L eK (fun _ ↦ j) _).le) (ρ.s _).isUnit
    ((coe_res_pullGen L (fun _ ↦ e) _ ρ _ (fun _ ↦ a₀) inf_le_right).symm.trans
      (hc.symm.trans (coe_res_pullGen L (fun _ ↦ j) _ r eK (fun _ ↦ a₀) inf_le_left)))
  refine ⟨⟨fun a ↦ (hsu a).unit⟩, ⟨fun a b ↦ Units.ext (hsc a b), ?_⟩, ?_⟩
  · exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (hsr (a ⟨⟩)))
  · rintro ⟨r'⟩ ⟨h₁, h₂⟩
    have := huniq (fun a ↦ r' a) ⟨fun a ↦ Units.isUnit _, fun a b ↦ congrArg Units.val (h₁ a b),
      fun a ↦ congrArg (fun c : LB.Gen (L.pull j) ↦ (c.s fun _ ↦ a).val) h₂⟩
    exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (congrFun this a))

theorem existsUnique_zpow_mul_chart (hϖ : Irreducible ϖ) {ι : Type v} {U : ι → H.Opens}
    {g : ∀ a b, Γ(H, U a ⊓ U b)} {W : ι → HK.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
    (hU : ∀ x : H, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b)) {r : ∀ a, Γ(HK, W a)}
    (hr : ∀ a b, HK.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        HK.presheaf.map (homOfLE inf_le_right).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(H, U a),
      (∀ a b, H.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * H.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, j.appLE (U a) (W a) (hW a).le (s a) =
        HK.presheaf.map (homOfLE le_top).op (fK.appTop ((Scheme.ΓSpecIso (.of K)).inv (algebraMap V K ϖ ^ n))) * r a) ∧
      ∃ a, ∃ x, f x = closedPoint V ∧ x ∈ H.basicOpen (s a) := by
  have := isOpenImmersion_generic hK
  have := isIntegral hK
  have := isLocallyNoetherian f
  have h0 : algebraMap V K ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hϖ.ne_zero
  let φ : K →+* Γ(HK, ⊤) := fK.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  have hτ : ∀ n : ℤ, ((Units.map φ.toMonoidHom (Units.mk0 _ h0) ^ n : Γ(HK, ⊤)ˣ) : Γ(HK, ⊤)) =
      fK.appTop ((Scheme.ΓSpecIso (.of K)).inv (algebraMap V K ϖ ^ n)) := fun n ↦ by
    rw [← map_zpow, Units.coe_map, Units.val_zpow_eq_zpow_val]
    rfl
  have := existsUnique_zpow_mul_appLE (notMem_basicOpen_iff_specializes hϖ hs)
    (prime_res_generic hϖ hs) (opensRange_generic hϖ hK) hW hU hg
    (Units.map φ.toMonoidHom (Units.mk0 _ h0)) (appTop_cst hK.w ϖ).symm hr hr0
  simpa only [hτ, notMem_basicOpen_iff f hϖ] using this

theorem existsUnique_zpow_mul_sec (hϖ : Irreducible ϖ) {L : LB H} (hL : L.IsLB)
    (r : (L.pull j).Sec) (hr0 : ∃ a, r.f a ≠ 0) :
    ∃! n : ℤ, ∃ s : L.Sec,
      (∀ a : PUnit → L.ι, j.appLE (L.U (a ⟨⟩)) ((L.pull j).U a) (pull_U L j a).le (s.f (a ⟨⟩)) =
        HK.presheaf.map (homOfLE le_top).op (fK.appTop ((Scheme.ΓSpecIso (.of K)).inv (algebraMap V K ϖ ^ n))) * r.f a) ∧
      ∃ a, ∃ x, f x = closedPoint V ∧ x ∈ H.basicOpen (s.f a) := by
  obtain ⟨n, ⟨s, hc, hsr, hx⟩, huniq⟩ := existsUnique_zpow_mul_chart hK hs hϖ
    (U := L.U) (g := fun a b ↦ L.g a b) (W := fun a ↦ (L.pull j).U fun _ ↦ a)
    (fun a ↦ pull_U L j _) (LB.mem_of_cover hL) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ r.f fun _ ↦ a)
    (fun a b ↦ by
      rw [← coe_pull_g L j (fun _ ↦ a) (fun _ ↦ b)]
      exact r.compat _ _)
    (hr0.elim fun a ha ↦ ⟨a ⟨⟩, ha⟩)
  refine ⟨n, ⟨⟨s, hc⟩, fun a ↦ hsr (a ⟨⟩), hx⟩, ?_⟩
  rintro m ⟨s', hsr', hx'⟩
  exact huniq m ⟨s'.f, s'.compat, fun a ↦ hsr' fun _ ↦ a, hx'⟩

end Main

theorem isIntegral_of_geometricallyIntegral {X S Z : Scheme.{u}} {q : X ⟶ S}
    [GeometricallyIntegral q] {F : Type u} [Field F] {y : Spec (.of F) ⟶ S} {k : Z ⟶ X}
    {p : Z ⟶ Spec (.of F)} (h : IsPullback k p q y) : IsIntegral Z :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ h

end GlobalTheory.DvrModel

namespace GlobalTheory.PrimeElement

end GlobalTheory.PrimeElement

namespace GlobalTheory.DvrModel

end GlobalTheory.DvrModel
