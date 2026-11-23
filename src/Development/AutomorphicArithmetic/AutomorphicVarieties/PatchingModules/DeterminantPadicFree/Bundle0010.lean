module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SelfdualRamified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0009
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.MemPowSmul
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mem_pow_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A) (N : ℕ) (x : M) :
    x ∈ (Ideal.span {t} ^ N • (⊤ : Submodule A M)) ↔ ∃ y, t ^ N • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

private theorem mem_X_pow_smul_of_X_smul_mem_X_pow_succ_smul {K M : Type} [Field K] [AddCommGroup M] [Module (PowerSeries K) M]
    [Module.Free (PowerSeries K) M] (N : ℕ) (v : M)
    (h : (PowerSeries.X : PowerSeries K) • v ∈
      (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ (N + 1) • (⊤ : Submodule (PowerSeries K) M))) :
    v ∈ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N • (⊤ : Submodule (PowerSeries K) M)) := by
  obtain ⟨u, hu⟩ := (mem_pow_smul _ _ _).1 h
  rw [mem_pow_smul]
  refine ⟨u, ?_⟩
  have hX : (PowerSeries.X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero
  apply smul_right_injective M hX
  dsimp only
  rw [← hu, smul_smul, ← pow_succ']

private theorem finite_quotient_X_pow_one_smul_module_of_free {K M : Type} [Field K] [Finite K] [AddCommGroup M] [Module (PowerSeries K) M]
    [Module.Free (PowerSeries K) M] [Module.Finite (PowerSeries K) M] :
    Finite (M ⧸ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 • (⊤ : Submodule (PowerSeries K) M))) := by
  classical
  let b := Module.Free.chooseBasis (PowerSeries K) M
  have key : ∀ (a : PowerSeries K) (v : M),
      (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 • (⊤ : Submodule (PowerSeries K) M)).mkQ (a • v) =
      (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 • (⊤ : Submodule (PowerSeries K) M)).mkQ
        (PowerSeries.C (PowerSeries.constantCoeff a) • v) := by
    intro a v
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← sub_smul]
    obtain ⟨c, hc⟩ := PowerSeries.X_dvd_iff.2
      (show PowerSeries.constantCoeff (a - PowerSeries.C (PowerSeries.constantCoeff a)) = 0 by simp)
    rw [hc, mem_pow_smul]
    exact ⟨c • v, by rw [pow_one, smul_smul]⟩
  apply Finite.of_surjective (fun c : Module.Free.ChooseBasisIndex (PowerSeries K) M → K =>
    (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 • (⊤ : Submodule (PowerSeries K) M)).mkQ
      (∑ i, PowerSeries.C (c i) • b i))
  intro m
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
  refine ⟨fun i => PowerSeries.constantCoeff (b.repr m i), ?_⟩
  dsimp only
  conv_rhs => rw [← b.sum_repr m]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  exact Finset.sum_congr rfl fun i _ => (key _ _).symm

private theorem eq_zero_of_forall_mem_X_pow_smul_module {K M : Type} [Field K] [AddCommGroup M] [Module (PowerSeries K) M]
    [Module.Finite (PowerSeries K) M] (x : M)
    (h : ∀ n : ℕ, x ∈ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ n • (⊤ : Submodule (PowerSeries K) M))) :
    x = 0 := by
  have hne : Ideal.span {(PowerSeries.X : PowerSeries K)} ≠ ⊤ := by
    intro htop
    have h1 : (1 : PowerSeries K) ∈ Ideal.span {(PowerSeries.X : PowerSeries K)} := htop ▸ Submodule.mem_top
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at h1
    simp at h1
  have := IsHausdorff.of_isLocalRing (Ideal.span {(PowerSeries.X : PowerSeries K)}) M hne
  exact this.haus x fun n => SModEq.sub_mem.2 (by simpa using h n)

theorem UpperTheory.V.Pa.Det.z1Fg :
    ∀ (l : ℕ) [Fact l.Prime] {K G M : Type} [Field K] [Finite K] [CharP K l] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [AddCommGroup M] [Module (PowerSeries K) M] [Module.Free (PowerSeries K) M] [Module.Finite (PowerSeries K) M] (ρ : G →* Module.End (PowerSeries K) M) (Z : Submodule (PowerSeries K) (G → M)), PhiCond G l → (∀ (N : ℕ) m, IsLocallyConstant fun g => (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N • (⊤ : Submodule (PowerSeries K) M)).mkQ (ρ g m)) → (∀ z ∈ Z, (∀ N : ℕ, IsLocallyConstant fun g => (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N • (⊤ : Submodule (PowerSeries K) M)).mkQ (z g)) ∧ ∀ g h, z (g * h) = z g + ρ g (z h)) → Z.FG := by
  intro l _ K G M _ _ _ _ _ _ _ _ _ _ _ _ ρ Z hΦ hρ hZ
  let C : Submodule (PowerSeries K) (G → M) :=
    { carrier := {z | (∀ N : ℕ, IsLocallyConstant fun g =>
          (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N • (⊤ : Submodule (PowerSeries K) M)).mkQ (z g)) ∧
          ∀ g h, z (g * h) = z g + ρ g (z h)}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · convert (ha1 N).add (hb1 N) using 1
          funext g
          simp
        · simp only [Pi.add_apply, ha2, hb2, map_add (f := _)]
          abel
      zero_mem' := by
        refine ⟨fun N => ?_, fun g h => by simp⟩
        convert IsLocallyConstant.const (X := G) (0 : M ⧸ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N •
          (⊤ : Submodule (PowerSeries K) M))) using 1
        funext g
        simp
      smul_mem' := by
        rintro c a ⟨ha1, ha2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · convert (ha1 N).comp (fun x => c • x) using 1
          funext g
          simp
        · simp only [Pi.smul_apply, ha2, map_smul, smul_add] }
  have hZC : Z ≤ C := fun z hz => hZ z hz
  have hH : IsHausdorff (Ideal.span {(PowerSeries.X : PowerSeries K)}) C := by
    refine ⟨fun x hx => ?_⟩
    ext g
    refine eq_zero_of_forall_mem_X_pow_smul_module (K := K) (x.1 g) fun n => ?_
    have h1 := SModEq.sub_mem.1 (hx n)
    rw [sub_zero, mem_pow_smul] at h1
    obtain ⟨y, hy⟩ := h1
    rw [mem_pow_smul]
    exact ⟨y.1 g, by rw [← hy]; rfl⟩
  let Φ : C →ₗ[PowerSeries K] (G → M ⧸ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 •
      (⊤ : Submodule (PowerSeries K) M))) :=
    LinearMap.pi (fun g => (Submodule.mkQ _) ∘ₗ LinearMap.proj g) ∘ₗ C.subtype
  have hker : LinearMap.ker Φ ≤
      Ideal.span {(PowerSeries.X : PowerSeries K)} • (⊤ : Submodule (PowerSeries K) C) := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := z.2
    have hz' : ∀ g, z.1 g ∈ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 •
        (⊤ : Submodule (PowerSeries K) M)) := fun g => by
      have := congr_fun (LinearMap.mem_ker.1 hz) g
      exact (Submodule.Quotient.mk_eq_zero _ (x := z.1 g)).1 this
    choose w hw using fun g => (mem_pow_smul _ _ _).1 (hz' g)
    have hw' : ∀ g, (PowerSeries.X : PowerSeries K) • w g = z.1 g := fun g => by simpa using hw g
    have hwC : w ∈ C := by
      change _ ∧ _
      refine ⟨fun N => ?_, fun g h => ?_⟩
      · rw [IsLocallyConstant.iff_eventually_eq]
        intro g
        filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hz1 (N + 1)) g] with g' hg'
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hg' ⊢
        apply mem_X_pow_smul_of_X_smul_mem_X_pow_succ_smul N
        rw [smul_sub, hw', hw']
        exact hg'
      · apply smul_right_injective M (PowerSeries.X_ne_zero (R := K))
        dsimp only
        rw [smul_add, ← LinearMap.map_smul (ρ g), hw', hw', hw']
        exact hz2 g h
    rw [show Ideal.span {(PowerSeries.X : PowerSeries K)} = Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 from
      (pow_one _).symm, mem_pow_smul]
    exact ⟨⟨w, hwC⟩, by ext g; simpa using hw' g⟩
  have hle : Ideal.span {(PowerSeries.X : PowerSeries K)} • (⊤ : Submodule (PowerSeries K) C) ≤
      LinearMap.ker Φ := by
    intro z hz
    rw [show Ideal.span {(PowerSeries.X : PowerSeries K)} = Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 from
      (pow_one _).symm, mem_pow_smul] at hz
    obtain ⟨y, rfl⟩ := hz
    rw [LinearMap.mem_ker]
    funext g
    show (Submodule.mkQ _) (((PowerSeries.X : PowerSeries K) ^ 1 • y).1 g) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_pow_smul]
    exact ⟨y.1 g, rfl⟩
  let ρbar : G →* AddMonoid.End (M ⧸ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 •
      (⊤ : Submodule (PowerSeries K) M))) :=
    { toFun := fun g => (Submodule.mapQ _ _ (ρ g)
          (Submodule.smul_top_le_comap_smul_top _ (ρ g))).toAddMonoidHom
      map_one' := by
        refine AddMonoidHom.ext fun x => ?_
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
        simp
        rfl
      map_mul' := by
        intro g h
        refine AddMonoidHom.ext fun x => ?_
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
        simp
        rfl }
  haveI := finite_quotient_X_pow_one_smul_module_of_free (K := K) (M := M)
  have hl' : ∀ m : M ⧸ (Ideal.span {(PowerSeries.X : PowerSeries K)} ^ 1 •
      (⊤ : Submodule (PowerSeries K) M)), l • m = 0 := by
    intro m
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
    have hl0 : ((l : ℕ) : PowerSeries K) = 0 := by
      rw [← map_natCast (PowerSeries.C (R := K)), CharP.cast_eq_zero, map_zero]
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (PowerSeries K), hl0, zero_smul, map_zero]
  have hloc : ∀ m, IsLocallyConstant fun g => ρbar g m := by
    intro m
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
    first
      | exact hρ 1 m
      | (convert hρ 1 m using 1; funext g; simp [ρbar])
  let Ψ := (Ideal.span {(PowerSeries.X : PowerSeries K)} • (⊤ : Submodule (PowerSeries K) C)).liftQ Φ hle
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker
  have hrange : Set.range Ψ ⊆ {w | IsLocallyConstant w ∧ ∀ g h, w (g * h) = w g + ρbar g (w h)} := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨hz1, hz2⟩ := z.2
    refine ⟨hz1 1, fun g h => ?_⟩
    show Submodule.mkQ _ (z.1 (g * h)) = Submodule.mkQ _ (z.1 g) + Submodule.mkQ _ (ρ g (z.1 h))
    rw [hz2, map_add (f := _)]
  have hS := Det.locallyConstant_cocycles_finite_of_phi l ρbar hΦ hl' hloc
  haveI : Finite (Set.range Ψ) := (hS.subset hrange).to_subtype
  haveI : Finite (C ⧸ Ideal.span {(PowerSeries.X : PowerSeries K)} • (⊤ : Submodule (PowerSeries K) C)) :=
    Finite.of_injective_finite_range hinj
  haveI : Module.Finite (PowerSeries K)
      (C ⧸ Ideal.span {(PowerSeries.X : PowerSeries K)} • (⊤ : Submodule (PowerSeries K) C)) :=
    Module.Finite.of_finite
  haveI := hH
  have hCfin : Module.Finite (PowerSeries K) C :=
    (UpperTheory.V.abelian₂.nakayama (PowerSeries K) (Ideal.span {(PowerSeries.X : PowerSeries K)}) C).2 inferInstance
  haveI := isNoetherian_of_isNoetherianRing_of_finite (PowerSeries K) C
  have hfg : (Z.comap C.subtype).FG := IsNoetherian.noetherian _
  have := hfg.map C.subtype
  rwa [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hZC] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.OneBlock
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem henselian_powerSeries (K : Type) [Field K] : HenselianLocalRing (PowerSeries K) := by
  have hR : HenselianRing (PowerSeries K) (Ideal.span {PowerSeries.X}) := inferInstance
  refine { toIsLocalRing := inferInstance, is_henselian := fun f hf a₀ h₁ h₂ => ?_ }
  rw [PowerSeries.maximalIdeal_eq_span_X] at h₁ ⊢
  exact hR.is_henselian f hf a₀ h₁ (h₂.map _)

private theorem coe_generalLinearGroup_map_eq_map {R S : Type} [CommRing R] [CommRing S] {m : ℕ} (f : R →+* S)
    (g : GL (Fin m) R) :
    ((GeneralLinearGroup.map f g : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) =
      (g : Matrix (Fin m) (Fin m) R).map f := by
  ext i j
  exact GeneralLinearGroup.map_apply f i j g

private theorem map_transpose_mul_mul_eq {R S : Type} [CommRing R] [CommRing S] {m : ℕ} (φ : R →+* S)
    (X Y Z : Matrix (Fin m) (Fin m) R) :
    (Xᵀ * Y * Z).map φ = (X.map φ)ᵀ * Y.map φ * Z.map φ := by
  simp [Matrix.map_mul, Matrix.transpose_map]

theorem UpperTheory.V.Pa.Det.oneBlock :
    ∀ {K K' G : Type} [Field K] [Field K'] [Group G] {m : ℕ} (j₁ : PowerSeries K →+* PowerSeries K) (f₁ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K)) (j₂ : PowerSeries K →+* PowerSeries K') (f₂ : FractionRing (PowerSeries K) →+* FractionRing (PowerSeries K')) (r : G →* GL (Fin m) (FractionRing (PowerSeries K))) (H : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K))) (σ : G → G) (u : G → PowerSeries K) (d : PowerSeries K), (2 : K) ≠ 0 → (∀ y, f₁ (algebraMap _ _ y) = algebraMap _ _ (j₁ y)) → (∀ y, f₂ (algebraMap _ _ y) = algebraMap _ _ (j₂ y)) → j₁ PowerSeries.X = PowerSeries.X ^ 2 → (∀ c : (PowerSeries K)ˣ, IsSquare (residue (PowerSeries K') (j₂ c))) → d ≠ 0 → (∀ g i i', ∃ y : PowerSeries K, algebraMap _ (FractionRing (PowerSeries K)) d * r g i i' = algebraMap _ (FractionRing (PowerSeries K)) y) → Hᵀ = H → H.det ≠ 0 → Function.Surjective σ → (∀ g, (mat r g)ᵀ * H * mat r (σ g) = algebraMap _ (FractionRing (PowerSeries K)) (u g) • H) → ∃ (Q : GL (Fin m) (FractionRing (PowerSeries K'))) (r' : G →* GL (Fin m) (PowerSeries K')), (Q : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K')))ᵀ * H.map (f₂.comp f₁) * Q = 1 ∧ (∀ g, pushRep (f₂.comp f₁) r g * Q = Q * pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) r' g) := by
  intro K K' G _ _ _ m j₁ f₁ j₂ f₂ r H σ u d h2 hf₁ hf₂ hj₁ hsq hd hdr hHs hdet hσ hsim
  obtain ⟨Q₀, r₀, hQ₀⟩ := Det.latInt r d hd hdr
  have hQ₀m : ∀ g, (r g).1 * Q₀.1 =
      Q₀.1 * (r₀ g).1.map (algebraMap _ _) := by
    intro g
    have := congr_arg Units.val (hQ₀ g)
    simpa only [Units.val_mul, pushRep, MonoidHom.comp_apply, coe_generalLinearGroup_map_eq_map] using this
  obtain ⟨H₁, hH₁⟩ : ∃ H₁ : Matrix (Fin m) (Fin m) (FractionRing (PowerSeries K)),
      H₁ = Q₀.1ᵀ * H * Q₀ := ⟨_, rfl⟩
  have hH₁s : H₁ᵀ = H₁ := by
    rw [hH₁, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hHs, Matrix.mul_assoc]
  have hQdet : Q₀.1.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 Q₀.isUnit).ne_zero
  have hH₁det : H₁.det ≠ 0 := by
    rw [hH₁, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hQdet hdet) hQdet
  have hsim₀ : ∀ g, ((r₀ g).1.map
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))ᵀ * H₁ *
      (r₀ (σ g)).1.map
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) =
      algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (u g) • H₁ := by
    intro g
    have key := hsim g
    simp only [mat, MonoidHom.comp_apply, Units.coeHom_apply] at key
    rw [hH₁]
    calc _ = (Q₀.1 *
            (r₀ g).1.map (algebraMap _ _))ᵀ * H *
          (Q₀.1 *
            (r₀ (σ g)).1.map (algebraMap _ _)) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ((r g).1 * Q₀.1)ᵀ * H *
          ((r (σ g)).1 * Q₀.1) := by
          rw [← hQ₀m, ← hQ₀m]
      _ = Q₀.1ᵀ *
          ((r g).1ᵀ * H *
            (r (σ g)).1) * Q₀.1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [key, Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨P, H', r', hP, hr'⟩ := UpperTheory.V.AlgebraTools.selfdual_ramified (A := PowerSeries K)
    (F := FractionRing (PowerSeries K)) H₁ r₀ σ u (A' := PowerSeries K)
    (F' := FractionRing (PowerSeries K)) j₁ f₁ PowerSeries.X PowerSeries.X PowerSeries.X_irreducible
    hj₁.symm hf₁ (IsFractionRing.injective _ _) hH₁s hH₁det hσ hsim₀
  have h2u : IsUnit (2 : PowerSeries K) := by
    rw [← map_ofNat (PowerSeries.C (R := K)) 2]
    exact (isUnit_iff_ne_zero.2 h2).map _
  have hH's : H'.1ᵀ = H' := by
    have e : (H'.1.map
        (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))ᵀ =
        H'.1.map (algebraMap _ _) := by
      rw [← hP, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.transpose_map, hH₁s, Matrix.mul_assoc]
    refine Matrix.ext fun i j => ?_
    exact IsFractionRing.injective _ (FractionRing (PowerSeries K)) (congr_fun (congr_fun e i) j)
  have hH'det : IsUnit H'.1.det :=
    (Matrix.isUnit_iff_isUnit_det _).1 H'.isUnit
  haveI := henselian_powerSeries K'
  obtain ⟨P₂, hP₂⟩ := UpperTheory.V.AlgebraTools.orthonormal_local j₂ H'.1
    h2u hH's hH'det hsq
  refine ⟨GeneralLinearGroup.map (f₂.comp f₁) Q₀ * GeneralLinearGroup.map f₂ P *
      GeneralLinearGroup.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) P₂,
    (MulAut.conj P₂⁻¹).toMonoidHom.comp (pushRep j₂ r'), ?_, ?_⟩
  · have s1 : (Q₀.1.map (f₂.comp f₁))ᵀ *
        H.map (f₂.comp f₁) * Q₀.1.map (f₂.comp f₁) =
        (H₁.map f₁).map f₂ := by
      rw [← map_transpose_mul_mul_eq, ← hH₁, Matrix.map_map]
      rfl
    have s2 : (P.1.map f₂)ᵀ * (H₁.map f₁).map f₂ *
        P.1.map f₂ =
        (H'.1.map j₂).map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) := by
      rw [← map_transpose_mul_mul_eq, hP, Matrix.map_map, Matrix.map_map]
      congr 1
      funext a
      exact hf₂ a
    have s3 : (P₂.1.map
        (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))))ᵀ *
        (H'.1.map j₂).map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) *
        P₂.1.map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) = 1 := by
      rw [← map_transpose_mul_mul_eq, hP₂, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Units.val_mul, Units.val_mul, coe_generalLinearGroup_map_eq_map, coe_generalLinearGroup_map_eq_map, coe_generalLinearGroup_map_eq_map]
    rw [← s3, ← s2, ← s1]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  · intro g
    have t1 := congr_arg (GeneralLinearGroup.map (f₂.comp f₁)) (hQ₀ g)
    rw [map_mul, map_mul] at t1
    have t2 : GeneralLinearGroup.map (f₂.comp f₁) (GeneralLinearGroup.map (algebraMap (PowerSeries K)
        (FractionRing (PowerSeries K))) (r₀ g)) * GeneralLinearGroup.map f₂ P =
        GeneralLinearGroup.map f₂ P * GeneralLinearGroup.map
          (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (GeneralLinearGroup.map j₂ (r' g)) := by
      apply Units.ext
      have t2m := congr_arg (fun M => Matrix.map M f₂) (hr' g)
      simp only [Matrix.map_mul, Matrix.map_map] at t2m
      simp only [Units.val_mul, pushRep, MonoidHom.comp_apply, coe_generalLinearGroup_map_eq_map, Matrix.map_map]
      have fe1 : (⇑(f₂.comp f₁) ∘ ⇑(algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) =
          (⇑f₂ ∘ fun a => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (j₁ a)) :=
        funext fun a => by simp [hf₁]
      have fe2 : (⇑(algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) ∘ ⇑j₂) =
          (⇑f₂ ∘ ⇑(algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) :=
        funext fun a => by simp [hf₂]
      rw [fe1, fe2]
      exact t2m
    simp only [pushRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv,
      inv_inv] at t1 ⊢
    calc _ = (GeneralLinearGroup.map (f₂.comp f₁) (r g) * GeneralLinearGroup.map (f₂.comp f₁) Q₀) *
          GeneralLinearGroup.map f₂ P *
          GeneralLinearGroup.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) P₂ := by
          simp only [mul_assoc]
      _ = _ := by
          rw [t1, mul_assoc (GeneralLinearGroup.map (f₂.comp f₁) Q₀), t2]
          group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Shapiro
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem shapiro_projection_twisted_cocycle {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (s : F)
    (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F) (hχ : ∀ g, χ (D.σ g) = χ g)
    (hs : s * s = 1) (hp : ∀ g, z (D.σ g) = s • (z g)ᵀ)
    (P : Matrix (Fin n) (Fin n) F → Matrix (Fin n) (Fin n) F)
    (hPP : ∀ Z, P (P Z) = P Z) (hPs : ∀ Z, P (s • Z) = s • P Z)
    (hPd : ∀ g, P (dTw χ D.r Y g) = dTw χ D.r (P Y) g)
    (hsum : ∀ g, P (z g) + (P (z g)ᵀ)ᵀ = z g)
    (h1 : P Y ∈ Od F F n D.a) (h2 : (P Y)ᵀ ∈ Od F F n D.a)
    (h : ∀ g, P (z g) = dTw χ D.r Y g) :
    ∃ Y' ∈ Od F F n D.a, s • Y'ᵀ = Y' ∧ ∀ g, z g = dTw χ D.r Y' g := by
  refine ⟨P Y + s • (P Y)ᵀ, Submodule.add_mem _ h1 (Submodule.smul_mem _ s h2), ?_, ?_⟩
  · rw [transpose_add, transpose_smul, transpose_transpose, smul_add, smul_smul, hs, one_smul,
      add_comm]
  · intro g
    have hA : ∀ k, dTw χ D.r (P Y) k = P (z k) := fun k => by
      rw [← hPd, ← h, hPP]
    have hzT : (z g)ᵀ = s • z (D.σ g) := by
      rw [hp, smul_smul, hs, one_smul]
    have hB : s • dTw χ D.r (P Y)ᵀ g = (P (z g)ᵀ)ᵀ := by
      rw [hzT, hPs, ← hA, Det.dSigma D χ (P Y) g hχ, transpose_smul, transpose_transpose]
    have hlin : dTw χ D.r (P Y + s • (P Y)ᵀ) g = dTw χ D.r (P Y) g + s • dTw χ D.r (P Y)ᵀ g := by
      simp only [dTw, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      module
    rw [hlin, hA, hB, hsum]

theorem UpperTheory.V.Pa.Det.shapiro :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (s : F) (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), (∀ g, χ (D.σ g) = χ g) → s * s = 1 → TwCoc χ D.r Set.univ z → (∀ g, z g ∈ Od F F n D.a) → (∀ g, z (D.σ g) = s • (z g)ᵀ) → ((∀ g, cV D.a (z g) = dTw χ D.r Y g) ∨ ∀ g, cV' D.a (z g) = dTw χ D.r Y g) → ∃ Y' ∈ Od F F n D.a, s • Y'ᵀ = Y' ∧ ∀ g, z g = dTw χ D.r Y' g := by
  intro F G _ _ n D χ s z Y hχ hs hz hod hp h
  obtain ⟨-, -, hd, hc⟩ := UpperTheory.V.Pa.Det.cornerCoc D χ Set.univ z hz
  have ht : ∀ Z : Matrix (Fin n) (Fin n) F, (cV' D.a Z)ᵀ = cV D.a Zᵀ := fun Z => by
    have := (hc Zᵀ).2.2.1
    rw [transpose_transpose] at this
    rw [← this, transpose_transpose]
  rcases h with h | h
  · refine shapiro_projection_twisted_cocycle D χ s z Y hχ hs hp (cV D.a) (fun Z => ?_) (fun Z => ?_) (fun g => (hd Y g).1)
      (fun g => ?_) (hc Y).1 ?_ h
    · ext i j
      simp only [cV, Matrix.of_apply]
      split_ifs <;> rfl
    · ext i j
      simp only [cV, Matrix.of_apply, Matrix.smul_apply]
      split_ifs <;> simp
    · rw [(hc _).2.2.1, transpose_transpose]
      exact (hc _).2.2.2 (hod g)
    · rw [(hc _).2.2.1]
      exact (hc _).2.1
  · refine shapiro_projection_twisted_cocycle D χ s z Y hχ hs hp (cV' D.a) (fun Z => ?_) (fun Z => ?_) (fun g => (hd Y g).2)
      (fun g => ?_) (hc Y).2.1 ?_ h
    · ext i j
      simp only [cV', Matrix.of_apply]
      split_ifs <;> rfl
    · ext i j
      simp only [cV', Matrix.of_apply, Matrix.smul_apply]
      split_ifs <;> simp
    · rw [ht, transpose_transpose, add_comm]
      exact (hc _).2.2.2 (hod g)
    · rw [ht]
      exact (hc _).1
end

