module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.BaseBc
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem free_fin_transfer {S T N N' : Type} [CommRing S] [CommRing T] [AddCommGroup N] [AddCommGroup N']
    [Module S N] [Module T N'] [Module.Free S N] [Module.Finite S N] (τ : S ≃+* T) (e : N ≃+ N')
    (he : ∀ a z, e (a • z) = τ a • e z) : Module.Free T N' ∧ Module.Finite T N' := by
  letI : Module S N' := Module.compHom N' (τ : S →+* T)
  let e' : N ≃ₗ[S] N' := { e with map_smul' := he }
  haveI : Module.Free S N' := Module.Free.of_equiv e'
  haveI : Module.Finite S N' := Module.Finite.equiv e'
  refine ⟨Module.Free.of_basis ((Module.Free.chooseBasis S N').mapCoeffs τ (fun _ _ => rfl)), ?_⟩
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := N')
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span S (s : Set N') := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ (hy trivial) (hz trivial)
  | smul a y _ hy => exact Submodule.smul_mem _ (τ a) (hy trivial)

private theorem fin_of_hom {S R M : Type} [CommRing S] [CommRing R] [AddCommGroup M] [Module S M] [Module R M]
    [Module.Finite S M] (f : S → R) (h : ∀ (a : S) (m : M), a • m = f a • m) : Module.Finite R M :=
  _root_.UpperTheory.Reformulated.B.Qh10.fin_of_hom f h

private theorem lamEmb_X (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (D : ℕ) (k : Fin D) :
    lamEmb O O' D (MvPowerSeries.X (.inr k)) = MvPowerSeries.X (.inr k) := by
  simp [lamEmb]

theorem UpperTheory.V.Pa.BC.base_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) → ∃ b' : TWBase u' (J.map (Til.ι O O' B)) Unit D, Nonempty (BaseRel b b' τ) := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D b τ hr hu hτ
  haveI := b.free
  haveI := b.fin
  haveI : IsNoetherianRing (abelian₂ O Empty D) := inferInstance
  haveI : Module.Finite B b.M := fin_of_hom b.lam b.smul_lam
  obtain ⟨e, -, he⟩ := UpperTheory.V.Pa.BC.til_mod O O' (abelian₂ O Empty D) B b.lam b.M b.smul_lam
  let lam' : abelian₂ O' Unit D →ₐ[O'] Til O O' B := (Til.map O' b.lam).comp (τ.symm : abelian₂ O' Unit D →ₐ[O'] _)
  have hlam : ∀ a, lam' (τ a) = Til.map O' b.lam a := fun a => by simp [lam']
  letI mL : Module (abelian₂ O' Unit D) (Til O O' B ⊗[B] b.M) := Module.compHom _ (lam' : abelian₂ O' Unit D →+* Til O O' B)
  have hff := free_fin_transfer (T := abelian₂ O' Unit D) (N' := Til O O' B ⊗[B] b.M) τ.toRingEquiv e (fun a z => by
    rw [he, ← hlam]; rfl)
  refine ⟨{ wt := ⟨b.wt.v, b.wt.i, b.wt.γ, fun k => algebraMap O O' (b.wt.c k)⟩
            wt_res := ?_
            lam := lam'
            segmentWeightExponent := ?_
            M := Til O O' B ⊗[B] b.M
            smul_lam := fun _ _ => rfl
            free := hff.1
            fin := hff.2
            supp := ?_ }, ⟨⟨rfl, hlam, LinearEquiv.refl _ _⟩⟩⟩
  · intro k
    have h := congrArg (ResidueField.map (algebraMap O O')) (b.wt_res k)
    rw [map_mul, map_one, ResidueField.map_residue] at h
    dsimp only
    rw [hr.2.1]
    exact h
  · intro k
    dsimp only
    rw [← lamEmb_X O O' D k, ← hτ, hlam, Til.map_ι, b.segmentWeightExponent, map_sub, map_mul, map_one, Til.ι_algebraMap, ← hu.2]
    rfl
  · intro p hp
    have h1 := UpperTheory.V.AlgebraTools.mem_support_baseChange B (Til O O' B) b.M ⟨p, hp⟩
    rw [Module.mem_support_iff_of_finite, Module.mem_support_iff_of_finite] at h1
    rw [Ideal.map_le_iff_le_comap, ← b.supp _ (Ideal.comap_isPrime _ _)]
    exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ClosureBc
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem cbc_krull {B E : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [AddCommGroup E]
    [Module B E] [Module.Finite B E] (x : E)
    (hx : ∀ N : ℕ, x ∈ (maximalIdeal B ^ N) • (⊤ : Submodule B E)) : x = 0 := by
  have h := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := E) (maximalIdeal B) (maximalIdeal.isMaximal B).ne_top
  rw [← Submodule.mem_bot B, ← h, Submodule.mem_iInf]
  exact hx

private theorem cbc_lin {B E : Type} [CommRing B] [AddCommGroup E] [Module B E] (I : Ideal B)
    (f : E →ₗ[B] E) {x : E} (hx : x ∈ I • (⊤ : Submodule B E)) : f x ∈ I • (⊤ : Submodule B E) := by
  have h1 : f x ∈ (I • (⊤ : Submodule B E)).map f := Submodule.mem_map_of_mem hx
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl le_top h1

private theorem cbc_span {B R E : Type} [CommRing B] [Ring R] [Algebra B R] [Ring E] [Algebra B E]
    (π : R →ₐ[B] E) (I : Ideal B) (S : Set R)
    (hS : ∀ s ∈ S, π s ∈ I • (⊤ : Submodule B E)) {y : R}
    (hy : y ∈ TwoSidedIdeal.span S) : π y ∈ I • (⊤ : Submodule B E) := by
  induction hy using TwoSidedIdeal.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | left_absorb a x _ hx =>
    rw [map_mul]
    exact cbc_lin I (LinearMap.mulLeft B (π a)) hx
  | right_absorb a x _ hx =>
    rw [map_mul]
    exact cbc_lin I (LinearMap.mulRight B (π a)) hx

private theorem cbc_sub {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (I : Ideal A)
    (S : Set (MonoidAlgebra A G)) {x : MonoidAlgebra A G} (hx : x ∈ S) : x ∈ closureIdeal I S := by
  simp only [closureIdeal, TwoSidedIdeal.mem_iInf]
  exact fun N H => TwoSidedIdeal.subset_span (Or.inl (Or.inl hx))

private theorem cbc_zero {n : ℕ} {B G : Type} [CommRing B] [IsLocalRing B] [Group G] [TopologicalSpace G]
    (D : GDet n B G) (Z : Set (MonoidAlgebra B G)) (x : MonoidAlgebra B G) :
    D.toQuot Z x = 0 ↔ x ∈ D.chBar Z := by
  rw [← map_zero (D.toQuot Z)]
  exact (RingCon.eq _).trans (TwoSidedIdeal.mem_iff _ _).symm

private theorem cbc_exists {B' R : Type} [CommRing B'] [Ring R] [Algebra B' R] (J : TwoSidedIdeal R) :
    ∃ π : R →ₐ[B'] J.ringCon.Quotient, Function.Surjective π ∧ ∀ x, π x = 0 ↔ x ∈ J := by
  refine ⟨{ J.ringCon.mk' with commutes' := fun _ => rfl }, fun x => Quot.inductionOn x fun z => ⟨z, rfl⟩, fun x => ?_⟩
  exact (RingCon.eq _).trans (TwoSidedIdeal.mem_iff _ _).symm

private theorem cbc_semi {B B' R R' E E' : Type} [CommRing B] [CommRing B'] [Ring R] [Ring R'] [Ring E] [Ring E']
    [Algebra B R] [Algebra B E] [Algebra B' R'] [Algebra B' E'] (g : B →+* B') (φ : R →+* R')
    (hφ : ∀ b, φ (algebraMap B R b) = algebraMap B' R' (g b)) (p : R →ₐ[B] E) (hp : Function.Surjective p)
    (π : R' →ₐ[B'] E') (hk : ∀ x, p x = 0 → π (φ x) = 0) :
    ∃ ψ : E →+* E', (∀ x, ψ (p x) = π (φ x)) ∧ ∀ (b : B) (x : E), ψ (b • x) = g b • ψ x := by
  let ψ : E →+* E' := (p : R →+* E).liftOfSurjective hp ⟨(π : R' →+* E').comp φ, fun x hx => hk x hx⟩
  have h1 : ∀ x, ψ (p x) = π (φ x) := fun x =>
    RingHom.liftOfRightInverse_comp_apply (p : R →+* E) _ _ _ x
  refine ⟨ψ, h1, fun b x => ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← p.commutes, h1, hφ, π.commutes]

theorem UpperTheory.V.Pa.BC.closure_bc :
    ∀ (n h : ℕ) (B B' : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [CommRing B'] [IsLocalRing B'] [IsNoetherianRing B'] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n B G) (χ : Fin n → G →* (ResidueField B)ˣ), D.IsCont (maximalIdeal B) → D.map (residue B) = GDet.ofChars χ → UpperTheory.V.CA.MultFree χ h → ∀ (g : B →+* B') [IsLocalHom g] (Z : Set (MonoidAlgebra B G)) (Z' : Set (MonoidAlgebra B' G)), (∀ z ∈ Z', z ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G g '' {y | y ∈ D.chBar Z})) → ∀ z ∈ (D.map g).chBar Z', z ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G g '' {y | y ∈ D.chBar Z}) := by
  intro n h B B' _ _ _ _ _ _ _ _ G _ _ _ _ _ D χ hc hr hm g _ Z Z' hZ' z hz
  obtain ⟨⟨s, -, hs⟩, -, hU⟩ := UpperTheory.V.CA.finE D χ hc hr hm Z
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G g '' {y | y ∈ D.chBar Z}) with hJ
  obtain ⟨π, hπ, hπ0⟩ := cbc_exists (B' := B') J
  have hsurj : Function.Surjective (D.toQuot Z) := fun x => Quot.inductionOn x fun z => ⟨z, rfl⟩
  have hsing : ∀ u : G, MonoidAlgebra.mapRingHom G g (MonoidAlgebra.single u 1) = MonoidAlgebra.single u 1 := by
    intro u
    simp
  obtain ⟨ψ, hψ, hψs⟩ := cbc_semi g (MonoidAlgebra.mapRingHom G g) (fun b => by simp)
    (D.toQuot Z) hsurj π (fun x hx => (hπ0 _).2 (TwoSidedIdeal.subset_span ⟨x, (cbc_zero D Z x).1 hx, rfl⟩))
  have hsp : ∀ x, ψ x ∈ Submodule.span B' ((fun u => π (MonoidAlgebra.single u 1)) '' (s : Set G)) := by
    intro x
    have hx : x ∈ Submodule.span B ((fun g => D.toQuot Z (MonoidAlgebra.single g 1)) '' (s : Set G)) :=
      hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      rw [hψ, hsing]
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [hψs]; exact Submodule.smul_mem _ _ hx
  have hfin : Module.Finite B' J.ringCon.Quotient := by
    refine ⟨Submodule.fg_def.2 ⟨_, s.finite_toSet.image (fun u => π (MonoidAlgebra.single u 1)), ?_⟩⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hπ x
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)
    | single u a =>
      have : (MonoidAlgebra.single u a : MonoidAlgebra B' G) = a • MonoidAlgebra.single u 1 := by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [this, map_smul]
      refine Submodule.smul_mem _ _ ?_
      have := hsp (D.toQuot Z (MonoidAlgebra.single u 1))
      rwa [hψ, hsing] at this
  refine (hπ0 z).1 (cbc_krull (B := B') _ fun N => ?_)
  obtain ⟨U, hU⟩ := hU N
  simp only [GDet.chBar, closureIdeal, TwoSidedIdeal.mem_iInf] at hz
  refine cbc_span π _ _ ?_ (hz N U)
  rintro t (((ht | ht) | ⟨a, ha, rfl⟩) | ⟨u, hu, rfl⟩)
  · have h1 : t ∈ TwoSidedIdeal.span (D.map g).CH := TwoSidedIdeal.subset_span ht
    rw [UpperTheory.V.CA.g_chmap] at h1
    have h2 : t ∈ J := TwoSidedIdeal.span_mono (Set.image_mono fun y hy => cbc_sub _ _ (Or.inl hy)) h1
    rw [(hπ0 t).2 h2]
    exact zero_mem _
  · rw [(hπ0 t).2 (hZ' t ht)]
    exact zero_mem _
  · have : (MonoidAlgebra.single 1 a : MonoidAlgebra B' G) = a • 1 := by
      rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · have hle : (maximalIdeal B ^ N).map g ≤ maximalIdeal B' ^ N := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun a ha => Ideal.mem_comap.2 (map_nonunit g a ha)) N
    have key : ∀ x ∈ (maximalIdeal B ^ N) • (⊤ : Submodule B (D.CHQuot Z)),
        ψ x ∈ (maximalIdeal B' ^ N) • (⊤ : Submodule B' J.ringCon.Quotient) := by
      intro x hx
      refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => ?_)
      · rw [hψs]
        exact Submodule.smul_mem_smul (hle (Ideal.mem_map_of_mem g ha)) Submodule.mem_top
      · rw [map_add]; exact add_mem hx hy
    have := key _ (hU u hu)
    rw [map_sub, map_one, hψ, hsing] at this
    rw [map_sub, map_one]
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.FreeBc
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem free_quotient_base_change (S T S' : Type) [CommRing S] [CommRing T] [Algebra S T] [CommRing S']
    (τ : T ≃+* S') (I : Ideal S) (rk : ℕ) (M : Type) [AddCommGroup M] [Module S M]
    (e : M ≃ₗ[S] (Fin rk → S ⧸ I)) (I' : Ideal S')
    (hI : I' = I.map ((τ : T →+* S').comp (algebraMap S T))) :
    ∃ e' : T ⊗[S] M ≃+ (Fin rk → S' ⧸ I'), ∀ z m, e' (z • m) = τ z • e' m := by
  let J : Ideal T := I.map (algebraMap S T)
  have hJ : I' = J.map (τ : T →+* S') := by
    rw [hI, Ideal.map_map]
  let q : T ⧸ J ≃+* S' ⧸ I' := Ideal.quotientEquiv J I' τ hJ
  let A1 : T ⊗[S] M ≃ₗ[T] T ⊗[S] (Fin rk → S ⧸ I) := LinearEquiv.baseChange S T M _ e
  let A2 : T ⊗[S] (Fin rk → S ⧸ I) ≃ₗ[T] (Fin rk → T ⊗[S] (S ⧸ I)) :=
    (Algebra.TensorProduct.piRight S T T (fun _ : Fin rk => S ⧸ I)).toLinearEquiv
  let A3 : (Fin rk → T ⊗[S] (S ⧸ I)) ≃ₗ[T] (Fin rk → T ⧸ J) :=
    LinearEquiv.piCongrRight (fun _ => (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).symm.toLinearEquiv)
  let A := (A1.trans A2).trans A3
  refine ⟨A.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => q.toAddEquiv), ?_⟩
  intro z m
  funext i
  change q ((A (z • m)) i) = τ z • q ((A m) i)
  rw [A.map_smul, Pi.smul_apply]
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (A m i)
  rw [← hx, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, Ideal.quotientEquiv_mk, Ideal.quotientEquiv_mk, ← map_mul, map_mul]

theorem UpperTheory.V.Pa.BC.free_bc :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (S R : Type) [CommRing S] [Algebra O S] [IsNoetherianRing S] [CommRing R] [Algebra O R] [IsNoetherianRing R] (s : S →ₐ[O] R) (M : Type) [AddCommGroup M] [Module R M] (I : Ideal S) (rk : ℕ) (e : M ≃+ (Fin rk → S ⧸ I)), (∀ z m, e (s z • m) = z • e m) → ∀ (S' : Type) [CommRing S'] (τ : Til O O' S ≃+* S') (I' : Ideal S'), I' = I.map ((τ : Til O O' S →+* S').comp (Til.ι O O' S)) → ∃ e' : Til O O' R ⊗[R] M ≃+ (Fin rk → S' ⧸ I'), ∀ z m, e' (Til.map O' s z • m) = τ z • e' m := by
  intro O O' _ _ _ _ S R _ _ _ _ _ _ s M _ _ I rk e he S' _ τ I' hI
  letI : Module S M := Module.compHom M s.toRingHom
  let eL : M ≃ₗ[S] (Fin rk → S ⧸ I) := e.toLinearEquiv (fun c x => he c x)
  haveI : Module.Finite S M := Module.Finite.equiv eL.symm
  obtain ⟨ε, -, hε⟩ := BC.til_mod O O' S R s M (fun a m => rfl)
  obtain ⟨f, hf⟩ := free_quotient_base_change S (Til O O' S) S' τ I rk M eL I' (by rw [Til.algebraMap_eq]; exact hI)
  refine ⟨ε.symm.trans f, ?_⟩
  intro z m
  have hsymm : ε.symm (Til.map O' s z • m) = z • ε.symm m := by
    apply ε.injective
    rw [hε, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rw [AddEquiv.trans_apply, hsymm, hf, AddEquiv.trans_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairMf
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.pair_mf :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid F O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B), PhiCond F.G₀ l → Finite (ResidueField B) ∧ (∃ (χ : Fin n → F.G₀ →* (ResidueField B)ˣ) (h : ℕ), u.D.map (residue B) = GDet.ofChars χ ∧ UpperTheory.V.CA.MultFree χ h) ∧ ∀ Z : Set (MonoidAlgebra B F.G₀), ∃ s : Finset F.G₀, ∀ y : MonoidAlgebra B F.G₀, ∃ c : F.G₀ → B, y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ u.D.chBar Z := by
  intro l _ F O _ _ _ _ _ n r B _ _ _ u hPhi
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  let e : ResidueField O ≃+* ResidueField B :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap O B)) (resMap_bijective O B)
  haveI hfin : Finite (ResidueField B) := Finite.of_equiv _ e.toEquiv
  haveI : CharP (ResidueField B) l :=
    charP_of_injective_ringHom (f := (e : ResidueField O →+* ResidueField B)) e.injective l
  have hE : Function.Injective (Units.map (e : ResidueField O →* ResidueField B)) :=
    Units.map_injective (f := (e : ResidueField O →* ResidueField B)) e.injective
  let χ : Fin n → F.G₀ →* (ResidueField B)ˣ :=
    fun i => (Units.map (e : ResidueField O →* ResidueField B)).comp (r.chib i)
  have hker : ∀ i, (χ i).ker = (r.chib i).ker := by
    intro i
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show Units.map (e : ResidueField O →* ResidueField B) (r.chib i g) = 1 ↔ r.chib i g = 1
    rw [← map_one (Units.map (e : ResidueField O →* ResidueField B)), hE.eq_iff]
  have hopen : ∀ i, IsOpen ((χ i).ker : Set F.G₀) := fun i => by
    rw [hker]
    exact r.chib_open i
  have hinj : Function.Injective χ := by
    intro i j hij
    exact r.chib_inj (MonoidHom.ext fun g => hE (DFunLike.congr_fun hij g))
  have hres : (residue B) = (e : ResidueField O →+* ResidueField B).comp (res O B : B →+* ResidueField O) :=
    RingHom.ext fun b => (e.apply_symm_apply (residue B b)).symm
  obtain ⟨-, hcomp, -, -⟩ := UpperTheory.V.CA.d_gmap u.D
  obtain ⟨-, -, -, hrep⟩ := UpperTheory.V.CA.d_gmap (GDet.ofRep (diagRep r.chib))
  have hmap : u.D.map (residue B) = GDet.ofChars χ := by
    rw [hres, ← hcomp, u.red]
    show (GDet.ofRep (diagRep r.chib)).map _ = GDet.ofRep (GDet.diagRep χ)
    rw [hrep]
    congr 1
    ext g i j
    simp [diagRep, GDet.diagRep, χ, Matrix.diagonal_apply]
    split_ifs <;> simp
  obtain ⟨h, hmf⟩ := UpperTheory.V.CA.exists_multFree_of_phiCond_of_injective_chars l χ hPhi hopen hinj
  refine ⟨hfin, ⟨χ, h, hmap, hmf⟩, fun Z => ?_⟩
  obtain ⟨⟨s, -, hs⟩, -, -⟩ := UpperTheory.V.CA.finE u.D χ u.cont hmap hmf Z
  refine ⟨s, fun y => ?_⟩
  have hy : u.D.toQuot Z y ∈ Submodule.span B
      ((fun g ↦ (u.D.toQuot Z) (MonoidAlgebra.single g 1)) '' (s : Set F.G₀)) := by
    rw [hs]
    exact Submodule.mem_top
  obtain ⟨c, hc, hcy⟩ := (Finsupp.mem_span_image_iff_linearCombination B).mp hy
  rw [Finsupp.linearCombination_apply_of_mem_supported B hc] at hcy
  refine ⟨c, ?_⟩
  have hz : u.D.toQuot Z (y - ∑ g ∈ s, MonoidAlgebra.single g (c g)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, ← hcy, sub_eq_zero]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [← map_smul, MonoidAlgebra.smul_single', mul_one]
  rw [TwoSidedIdeal.mem_iff]
  exact (u.D.chBar Z).ringCon.eq.mp hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.XmapsBc
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.xmaps_bc :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (R P : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] [CommRing P] [Algebra O P] [IsNoetherianRing P] (θ : R →ₐ[O] P) (X X0 : Type) [AddCommGroup X] [Module R X] [AddCommGroup X0] [Module P X0] (f : R) (φ : X0 →+ X) (ψ : X →+ X0), (∃ s : Finset X0, ∀ z, ∃ c : X0 → R, z = ∑ g ∈ s, θ (c g) • g) → (∀ (t : R) z, φ (θ t • z) = t • φ z) → (∀ (t : R) z, ψ (t • z) = θ t • ψ z) → (∀ z, φ (ψ z) = f • z) → (∀ z, ψ (φ z) = θ f • z) → ∃ (φ' : Til O O' P ⊗[P] X0 →+ Til O O' R ⊗[R] X) (ψ' : Til O O' R ⊗[R] X →+ Til O O' P ⊗[P] X0), (∀ t z, φ' (Til.map O' θ t • z) = t • φ' z) ∧ (∀ t z, ψ' (t • z) = Til.map O' θ t • ψ' z) ∧ (∀ z, φ' (ψ' z) = Til.ι O O' R f • z) ∧ ∀ z, ψ' (φ' z) = Til.map O' θ (Til.ι O O' R f) • z := by
  intro O O' _ _ _ _ R P _ _ _ _ _ _ θ X X0 _ _ _ _ f φ ψ hgen hφ hψ hφψ hψφ
  letI : Module R X0 := Module.compHom X0 θ.toRingHom
  haveI : Module.Finite R X0 := by
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hgen
    refine ⟨s, ?_⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨c, hc⟩ := hs z
    rw [hc]
    refine Submodule.sum_mem _ (fun g hg => ?_)
    exact Submodule.smul_mem _ (c g) (Submodule.subset_span hg)
  obtain ⟨e, he1, he2⟩ := BC.til_mod O O' R P θ X0 (fun a m => rfl)
  let φL : X0 →ₗ[R] X :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun t z => hφ t z }
  let ψL : X →ₗ[R] X0 :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := fun t z => hψ t z }
  let A := Til O O' R
  let Φ := LinearMap.baseChange A φL
  let Ψ := LinearMap.baseChange A ψL
  have hsc : ∀ (M : Type) [AddCommGroup M] [Module R M] (g : M →ₗ[R] M) (r : R), (∀ m, g m = r • m) →
      ∀ w : A ⊗[R] M, LinearMap.baseChange A g w = Til.ι O O' R r • w := by
    intro M _ _ g r hg w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, hg, ← Til.algebraMap_eq, ← TensorProduct.smul_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
    | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  have heinv : ∀ (t : A) (z : Til O O' P ⊗[P] X0), e.symm (Til.map O' θ t • z) = t • e.symm z := by
    intro t z
    apply e.injective
    rw [he2, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  refine ⟨Φ.toAddMonoidHom.comp e.symm.toAddMonoidHom, e.toAddMonoidHom.comp Ψ.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro t z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [heinv, LinearMap.map_smul]
  · intro t z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [LinearMap.map_smul, he2]
  · intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, AddEquiv.symm_apply_apply]
    have := hsc X (φL ∘ₗ ψL) f (fun m => hφψ m) z
    rw [LinearMap.baseChange_comp] at this
    exact this
  · intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    have := hsc X0 (ψL ∘ₗ φL) f (fun m => hψφ m) (e.symm z)
    rw [LinearMap.baseChange_comp] at this
    change e (Ψ (Φ (e.symm z))) = _
    rw [show Ψ (Φ (e.symm z)) = Til.ι O O' R f • e.symm z from this, he2, AddEquiv.apply_symm_apply]
end

