module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushoutResidueLinearIndependent
section
open IsLocalRing

namespace GlobalTheory

theorem pushout_residue_linearIndependent :
  ∀ (T D A B : Type) [CommRing T] [CommRing D] [CommRing A] [CommRing B] [IsLocalRing T] [IsLocalRing D] [Algebra T D] [Algebra T A] [Algebra D B] [Algebra A B] [Algebra T B] [IsScalarTower T D B] [IsScalarTower T A B] [Algebra.IsPushout T D A B], (maximalIdeal T).map (algebraMap T D) = maximalIdeal D → ∀ (n : ℕ) (x : Fin n → A), (∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T A) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, ∑ i, d i • algebraMap A B (x i) ∈ (maximalIdeal D).map (algebraMap D B) → ∀ i, d i ∈ maximalIdeal D := by
  intro T D A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTD n x hx d hd j

  haveI : IsLocalHom (algebraMap T D) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : a ∈ maximalIdeal T := (mem_maximalIdeal a).2 hna
    have h2 : algebraMap T D a ∈ maximalIdeal D := hTD ▸ Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).1 h2 ha
  letI : Field (T ⧸ maximalIdeal T) := Ideal.Quotient.field _

  let v : Fin n → A ⧸ (maximalIdeal T • (⊤ : Submodule T A)) := fun i => Submodule.Quotient.mk (x i)
  have hmem : ∀ y : A, y ∈ maximalIdeal T • (⊤ : Submodule T A) ↔
      y ∈ (maximalIdeal T).map (algebraMap T A) := by
    intro y; rw [Ideal.smul_top_eq_map]; rfl
  have hli : LinearIndependent (T ⧸ maximalIdeal T) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    obtain ⟨c', rfl⟩ : ∃ c' : Fin n → T, (fun k => Ideal.Quotient.mk (maximalIdeal T) (c' k)) = c :=
      ⟨fun k => (Ideal.Quotient.mk_surjective (c k)).choose,
        funext fun k => (Ideal.Quotient.mk_surjective (c k)).choose_spec⟩
    have hsum : (∑ k, Ideal.Quotient.mk (maximalIdeal T) (c' k) • v k) =
        Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) (∑ k, c' k • x k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Submodule.mkQ_apply, map_sum]
      rfl
    rw [hsum, Submodule.Quotient.mk_eq_zero, hmem] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hx c' hc i)

  let bs := Module.Basis.span hli
  obtain ⟨f, hf⟩ := LinearMap.exists_extend (K := T ⧸ maximalIdeal T) (bs.coord j)
  have hfv : ∀ i, f (v i) = if i = j then 1 else 0 := by
    intro i
    have := congrArg (fun F => F (bs i)) hf
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Module.Basis.coord_apply,
      Module.Basis.repr_self] at this
    rw [Module.Basis.span_apply] at this
    rw [this, Finsupp.single_apply]

  let φ : T ⧸ maximalIdeal T →+* ResidueField D := ResidueField.map (algebraMap T D)
  have hφ : ∀ t : T, φ (Ideal.Quotient.mk _ t) = algebraMap T (ResidueField D) t := fun t => rfl

  let g : A →ₗ[T] ResidueField D :=
    { toFun := fun a => φ (f (Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) a))
      map_add' := fun a b => by simp only [Submodule.Quotient.mk_add, map_add (f := _)]
      map_smul' := fun t a => by
        simp only [RingHom.id_apply]
        have hq : Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) (t • a) =
            Ideal.Quotient.mk (maximalIdeal T) t •
              Submodule.Quotient.mk (p := maximalIdeal T • (⊤ : Submodule T A)) a :=
          (Module.Quotient.mk_smul_mk A (maximalIdeal T) t a).symm
        rw [hq, map_smul, smul_eq_mul, map_mul, hφ, ← Algebra.smul_def] }
  have hg : ∀ i, g (x i) = if i = j then 1 else 0 := by
    intro i
    show φ (f (v i)) = _
    rw [hfv]; split_ifs <;> simp

  have hbc := (Algebra.IsPushout.out (R := T) (S := D) (R' := A) (S' := B))
  let ψ := hbc.lift g
  have hψ : ∀ a : A, ψ (algebraMap A B a) = g a := fun a => hbc.lift_eq g a
  have hkill : ∀ y ∈ (maximalIdeal D).map (algebraMap D B), ψ y = 0 := by
    intro y hy
    have hy' : y ∈ maximalIdeal D • (⊤ : Submodule D B) := by
      rw [Ideal.smul_top_eq_map]; exact hy
    refine Submodule.smul_induction_on hy' ?_ ?_
    · intro r hr b _
      rw [map_smul, Algebra.smul_def]
      have : algebraMap D (ResidueField D) r = 0 := (residue_eq_zero_iff r).2 hr
      rw [this, zero_mul]
    · intro a b ha hb; rw [map_add (f := _), ha, hb, add_zero]
  have := hkill _ hd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single j (fun i _ hi => by rw [map_smul, hψ, hg, if_neg hi, smul_zero])
    (by simp)] at this
  rw [map_smul, hψ, hg, if_pos rfl, Algebra.smul_def, mul_one] at this
  exact (residue_eq_zero_iff _).1 this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
section
noncomputable section

namespace GlobalTheory.HTRho

variable {k H O C : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O]

def mSub (σ : O →+* Module.End k H) (χ : C →+* k) (X : Submodule k H) : Submodule k H :=
  Submodule.span k {z | ∃ c : C, ∃ x ∈ X, z = σ (algebraMap C O c) x - χ c • x}

def jSub {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) (X : Submodule k H) : Submodule k H :=
  Submodule.span k {z | ∃ (r : ℕ) (lam : Fin r → k) (c : Fin r → C) (x : H), x ∈ X ∧
    (∀ i, ∑ l, lam l * χ i (c l) = 0) ∧ z = ∑ l, lam l • σ (algebraMap C O (c l)) x}

def homO {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) : Submodule k (X →ₗ[k] Y) where
  carrier := {T | ∀ a, T ∘ₗ σX a = σY a ∘ₗ T}
  zero_mem' a := by simp
  add_mem' {S T} hS hT a := by rw [LinearMap.add_comp, LinearMap.comp_add, hS a, hT a]
  smul_mem' c T hT a := by rw [LinearMap.smul_comp, LinearMap.comp_smul, hT a]

theorem mem_homO {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) (T : X →ₗ[k] Y) :
    T ∈ homO σX σY ↔ ∀ a x, T (σX a x) = σY a (T x) := by
  simp only [homO, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    LinearMap.ext_iff, LinearMap.comp_apply]

def rAct (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X) :
    O →+* Module.End k X where
  toFun a := (σ a).restrict (h a)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

def qAct (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X) :
    O →+* Module.End k (H ⧸ X) where
  toFun a := X.mapQ X (σ a) (fun x hx => h a x hx)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] theorem qAct_mk (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X)
    (a : O) (x : H) : qAct σ X h a (X.mkQ x) = X.mkQ (σ a x) := rfl

theorem mSub_stable (σ : O →+* Module.End k H) (χ : C →+* k) (X : Submodule k H)
    (hX : ∀ a, ∀ x ∈ X, σ a x ∈ X) : ∀ a, ∀ x ∈ mSub σ χ X, σ a x ∈ mSub σ χ X := by
  intro a x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, y, hy, rfl⟩ := hz
    refine Submodule.subset_span ⟨c, σ a y, hX a y hy, ?_⟩
    rw [map_sub, map_smul, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul,
      Algebra.commutes]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem jSub_stable {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) (X : Submodule k H)
    (hX : ∀ a, ∀ x ∈ X, σ a x ∈ X) : ∀ a, ∀ x ∈ jSub σ χ X, σ a x ∈ jSub σ χ X := by
  intro a x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, lam, c, y, hy, hc, rfl⟩ := hz
    refine Submodule.subset_span ⟨r, lam, c, σ a y, hX a y hy, hc, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, Algebra.commutes]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem qAct_mSub_algebraMap (σ : O →+* Module.End k H) (χ : C →+* k) (c : C) :
    qAct σ (mSub σ χ ⊤) (mSub_stable σ χ ⊤ (fun _ _ _ => trivial)) (algebraMap C O c) = χ c • 1 := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  change (mSub σ χ ⊤).mkQ (σ (algebraMap C O c) x) = χ c • (mSub σ χ ⊤).mkQ x
  rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨c, x, trivial, rfl⟩

end GlobalTheory.HTRho
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorInjectiveOfPowSmulEqBot
section
open TensorProduct LinearMap Function

namespace GlobalTheory.NilpotentFlat

theorem rTensor_lTensor_apply {R : Type} [CommRing R] {M M' A A' : Type} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup A] [Module R A] [AddCommGroup A']
    [Module R A'] (g : M →ₗ[R] M') (f : A →ₗ[R] A') (x : M ⊗[R] A) :
    rTensor A' g (lTensor M f x) = lTensor M' f (rTensor A g x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, rTensor_comp_lTensor, lTensor_comp_rTensor]

theorem rTensor_injective_of_flat_baseChange {A C M N' N : Type} [CommRing A] [CommRing C]
    [Algebra A C] [AddCommGroup M] [Module A M] [Module.Flat C (C ⊗[A] M)]
    [AddCommGroup N'] [AddCommGroup N] [Module C N'] [Module C N] [Module A N'] [Module A N]
    [IsScalarTower A C N'] [IsScalarTower A C N] (ι : N' →ₗ[C] N) (hι : Injective ι) :
    Injective ((ι.restrictScalars A).rTensor M) := by
  let e' := AlgebraTensorModule.cancelBaseChange A C C N' M
  let e := AlgebraTensorModule.cancelBaseChange A C C N M
  have h1 : Injective (ι.rTensor (C ⊗[A] M)) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hι
  have key : ∀ z, (ι.restrictScalars A).rTensor M (e' z) = e (ι.rTensor (C ⊗[A] M) z) := by
    intro z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul n t =>
      induction t with
      | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
      | tmul c b => simp [e, e']
  intro x y h
  obtain ⟨x, rfl⟩ := e'.surjective x
  obtain ⟨y, rfl⟩ := e'.surjective y
  rw [key, key] at h
  rw [h1 (e.injective h)]

theorem lTensor_injective_of_flat {A C F N' N : Type} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup F] [Module A F] [Module C F] [IsScalarTower A C F] [Module.Flat C F]
    [AddCommGroup N'] [AddCommGroup N] [Module A N'] [Module A N] (ι : N' →ₗ[A] N)
    (hι : Injective (ι.rTensor C)) : Injective (ι.lTensor F) := by
  let e' := AlgebraTensorModule.cancelBaseChange A C C F N'
  let e := AlgebraTensorModule.cancelBaseChange A C C F N
  have hι' : Injective (ι.baseChange C) := (LinearMap.lTensor_inj_iff_rTensor_inj (M := C) ι).mpr hι
  have h1 : Injective ((ι.baseChange C).lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hι'
  have key : ∀ z, ι.lTensor F (e' z) = e ((ι.baseChange C).lTensor F z) := by
    intro z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul n t =>
      induction t with
      | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
      | tmul c b => simp [e, e']
  intro x y h
  obtain ⟨x, rfl⟩ := e'.surjective x
  obtain ⟨y, rfl⟩ := e'.surjective y
  rw [key, key] at h
  rw [h1 (e.injective h)]

variable {B : Type} [CommRing B]

theorem rTensor_injective_of_extension {K L : Type} [AddCommGroup K] [Module B K]
    [AddCommGroup L] [Module B L] [Module.Flat B L] (i : K →ₗ[B] L)
    {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module B N₁] [AddCommGroup N₂] [Module B N₂]
    [AddCommGroup N₃] [Module B N₃] (g₁ : N₁ →ₗ[B] N₂) (g₂ : N₂ →ₗ[B] N₃)
    (hg : Exact g₁ g₂) (hg₁ : Injective g₁) (hg₂ : Surjective g₂)
    (h₁ : Injective (i.rTensor N₁)) (h₃ : Injective (i.rTensor N₃)) :
    Injective (i.rTensor N₂) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have h2 : g₂.lTensor K x = 0 := by
    apply (injective_iff_map_eq_zero _).mp h₃
    rw [rTensor_lTensor_apply, hx, map_zero]
  obtain ⟨x₁, rfl⟩ := (lTensor_exact K hg hg₂ x).mp h2
  have h4 : i.rTensor N₁ x₁ = 0 := by
    apply (injective_iff_map_eq_zero _).mp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := L) g₁ hg₁)
    rw [← rTensor_lTensor_apply, hx]
  simp [(injective_iff_map_eq_zero _).mp h₁ _ h4]

theorem rTensor_injective_quotient (I : Ideal B) {K L M : Type} [AddCommGroup K] [Module B K]
    [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M] (i : K →ₗ[B] L) (π : L →ₗ[B] M)
    (hi : Injective i) (hex : Exact i π) (hπ : Surjective π)
    (hIM : Injective (I.subtype.rTensor M)) : Injective (i.rTensor (B ⧸ I)) := by
  have h := lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I) hex hπ hIM
    (Module.Flat.lTensor_preserves_injective_linearMap (M := B) i hi)
  exact (lTensor_inj_iff_rTensor_inj (B ⧸ I) i).mp h

theorem rTensor_injective_of_quotient_module (I : Ideal B) {K L M : Type} [AddCommGroup K]
    [Module B K] [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M] (i : K →ₗ[B] L)
    (π : L →ₗ[B] M) (hex : Exact i π) (hπ : Surjective π)
    [Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M)] (hI : Injective (i.rTensor (B ⧸ I)))
    (N : Type) [AddCommGroup N] [Module (B ⧸ I) N] [Module B N] [IsScalarTower B (B ⧸ I) N] :
    Injective (i.rTensor N) := by
  let p : (N →₀ (B ⧸ I)) →ₗ[B ⧸ I] N := Finsupp.linearCombination (B ⧸ I) id
  have hp : Surjective p := fun n => ⟨Finsupp.single n 1, by simp [p]⟩
  have h := lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := (LinearMap.ker p).subtype.restrictScalars B) (f₂ := p.restrictScalars B)
    (LinearMap.exact_subtype_ker_map p) hp hex hπ
    (rTensor_injective_of_flat_baseChange (LinearMap.ker p).subtype (Submodule.injective_subtype _))
    (lTensor_injective_of_flat (C := B ⧸ I) (F := N →₀ (B ⧸ I)) i hI)
  exact (lTensor_inj_iff_rTensor_inj N i).mp h

theorem rTensor_injective_of_pow_smul_eq_bot (I : Ideal B) {K L : Type} [AddCommGroup K]
    [Module B K] [AddCommGroup L] [Module B L] [Module.Flat B L] (i : K →ₗ[B] L)
    (hbase : ∀ (N : Type) [AddCommGroup N] [Module (B ⧸ I) N] [Module B N]
      [IsScalarTower B (B ⧸ I) N], Injective (i.rTensor N)) (n : ℕ) :
    ∀ (N : Type) [AddCommGroup N] [Module B N], (I ^ n • ⊤ : Submodule B N) = ⊥ →
      Injective (i.rTensor N) := by
  induction n with
  | zero =>
    intro N _ _ hN
    have h0 : ∀ x : N, x = 0 := fun x => by
      have hx : x ∈ (I ^ 0 • ⊤ : Submodule B N) := by
        rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial
      rw [hN] at hx
      simpa using hx
    have hz : ∀ z : K ⊗[B] N, z = 0 := fun z => by
      induction z with
      | tmul k x => rw [h0 x, tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    intro a b _
    rw [hz a, hz b]
  | succ n ih =>
    intro N _ _ hN
    let S : Submodule B N := I • ⊤
    refine rTensor_injective_of_extension i S.subtype S.mkQ (LinearMap.exact_subtype_mkQ S)
      S.injective_subtype (Submodule.mkQ_surjective S) (ih S ?_) (hbase (N ⧸ S))
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_smul'', Submodule.map_bot, Submodule.map_subtype_top, ← Submodule.mul_smul,
      ← pow_succ, hN]

theorem flat_of_isNilpotent : ∀ (B : Type) [CommRing B] (I : Ideal B), IsNilpotent I →
    ∀ (M : Type) [AddCommGroup M] [Module B M],
      Module.Flat (B ⧸ I) (M ⧸ (I • ⊤ : Submodule B M)) →
      Function.Injective (TensorProduct.lift ((LinearMap.lsmul B M).comp I.subtype)) →
      Module.Flat B M := by
  intro B _ I hI M _ _ hflat hinj
  obtain ⟨n, hn⟩ := hI
  let π : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
  have hπ : Surjective π := fun m => ⟨Finsupp.single m 1, by simp [π]⟩
  let K := LinearMap.ker π
  have hex : Exact K.subtype π := LinearMap.exact_subtype_ker_map π
  have hIM : Injective (I.subtype.rTensor M) := by
    have e : TensorProduct.lift ((LinearMap.lsmul B M).comp I.subtype) =
        (TensorProduct.lid B M).toLinearMap ∘ₗ I.subtype.rTensor M := by
      ext a m
      simp
    rw [e, LinearMap.coe_comp] at hinj
    exact hinj.of_comp
  let e : ((B ⧸ I) ⊗[B] M) ≃ₗ[B ⧸ I] (M ⧸ (I • ⊤ : Submodule B M)) :=
    (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  haveI : Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M) := Module.Flat.of_linearEquiv e
  have hq := rTensor_injective_quotient I K.subtype π K.injective_subtype hex hπ hIM
  have hall := rTensor_injective_of_pow_smul_eq_bot I K.subtype
    (rTensor_injective_of_quotient_module I K.subtype π hex hπ hq) n
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  refine lTensor_injective_of_exact_of_exact_of_rTensor_injective hex hπ
    (LinearMap.exact_subtype_mkQ J) (Submodule.mkQ_surjective J) (hall (B ⧸ J) ?_)
    (Module.Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype)
  rw [hn, Submodule.zero_eq_bot, Submodule.bot_smul]

end GlobalTheory.NilpotentFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RadicalEltMovingDualToMajorant
section
open scoped ComplexOrder
open Matrix

namespace GlobalTheory

theorem radical_elt_moving_dual_to_majorant (n p : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J.conjTranspose = J) (hθ : θ * θ = 1) (hQ : (J * θ).PosDef)
    (X₂ Y₂ : Matrix (Fin n) (Fin p) ℂ) (hXX : X₂.conjTranspose * J * X₂ = 0)
    (hYY : Y₂.conjTranspose * J * Y₂ = 0) (hXY : X₂.conjTranspose * J * Y₂ = 1) :
    ∃ u₁ : GL (Fin n) ℂ, (u₁.1).conjTranspose * J * u₁.1 = J ∧ u₁.1 * X₂ = X₂ ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ w : Fin p → ℂ, Matrix.mulVec u₁.1 v - v = Matrix.mulVec X₂ w) ∧
      θ * X₂ = u₁.1 * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) := by
  have hθJ : θᴴ * J = J * θ := by
    have := hQ.isHermitian.eq
    rwa [conjTranspose_mul, hJ] at this
  have hYX : Y₂ᴴ * J * X₂ = 1 := by
    have := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hinj : Function.Injective X₂.mulVec := by
    intro a b hab
    have := congrArg (fun v => (Y₂ᴴ * J).mulVec v) hab
    simpa [Matrix.mulVec_mulVec, hYX] using this
  have hP : (X₂ᴴ * (J * θ) * X₂).PosDef := hQ.conjTranspose_mul_mul_same hinj
  obtain ⟨P, hPdef⟩ : ∃ P, P = X₂ᴴ * (J * θ) * X₂ := ⟨_, rfl⟩
  rw [← hPdef] at hP ⊢
  have hdet : IsUnit P.det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPiH : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.isHermitian.eq]
  obtain ⟨Y', hY'⟩ : ∃ Y', Y' = θ * X₂ * P⁻¹ := ⟨_, rfl⟩
  have hXY' : X₂ᴴ * J * Y' = 1 := by
    rw [← hPPi, hY', hPdef]; simp only [Matrix.mul_assoc]
  have hY'Y' : Y'ᴴ * J * Y' = 0 := by
    have h1 : ∀ B : Matrix (Fin n) (Fin p) ℂ, θᴴ * (J * (θ * B)) = J * B := by
      intro B
      rw [← Matrix.mul_assoc, hθJ, Matrix.mul_assoc, ← Matrix.mul_assoc θ, hθ, Matrix.one_mul]
    have h2 : X₂ᴴ * (J * (X₂ * P⁻¹)) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.zero_mul]
    rw [hY']
    simp only [conjTranspose_mul, hPiH, Matrix.mul_assoc, h1, h2, Matrix.mul_zero]
  obtain ⟨D, hD⟩ : ∃ D, D = Y' - Y₂ := ⟨_, rfl⟩
  have hXD : X₂ᴴ * J * D = 0 := by rw [hD, Matrix.mul_sub, hXY', hXY, sub_self]
  have hDX : Dᴴ * J * X₂ = 0 := by
    have := congrArg conjTranspose hXD
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hkey : Dᴴ * J * D + Dᴴ * J * Y₂ + Y₂ᴴ * J * D = 0 := by
    rw [hD]
    simp only [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc] at hY'Y' hYY ⊢
    rw [hY'Y', hYY]
    abel

  have tXX : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (X₂ * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have tXD : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (D * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXD, Matrix.zero_mul]
  have tDX : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), Dᴴ * (J * (X₂ * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDX, Matrix.zero_mul]
  have tXY : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (Y₂ * B)) = B := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have hXX' : X₂ᴴ * (J * X₂) = 0 := by rw [← Matrix.mul_assoc, hXX]
  have hXD' : X₂ᴴ * (J * D) = 0 := by rw [← Matrix.mul_assoc, hXD]
  have hDX' : Dᴴ * (J * X₂) = 0 := by rw [← Matrix.mul_assoc, hDX]
  have hXY'' : X₂ᴴ * (J * Y₂) = 1 := by rw [← Matrix.mul_assoc, hXY]
  obtain ⟨E, hE⟩ : ∃ E, E = Dᴴ * J * Y₂ := ⟨_, rfl⟩
  have hE' : Dᴴ * (J * Y₂) = E := by rw [hE, Matrix.mul_assoc]
  obtain ⟨u, hu⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ,
      u = 1 + (D * X₂ᴴ * J - X₂ * Dᴴ * J + X₂ * E * X₂ᴴ * J) := ⟨_, rfl⟩
  have huJ : uᴴ * J * u = J := by
    have hexp : uᴴ * J * u = J + J * X₂ * (Dᴴ * J * D + Dᴴ * J * Y₂ + Y₂ᴴ * J * D) * X₂ᴴ * J := by
      rw [hu, hE]
      simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_mul, conjTranspose_one,
        conjTranspose_conjTranspose, hJ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, tXX, tXD, tDX,
        hXX', hXD', hDX', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]
      abel
    rw [hexp, hkey]; simp
  have huX : u * X₂ = X₂ := by
    rw [hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, hXX', hDX',
      Matrix.mul_zero, add_zero, sub_zero]
  have huY : u * Y₂ = Y' := by
    rw [hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, hXY'',
      Matrix.mul_one, hE']
    rw [hD]; abel
  have hdetJ : J.det ≠ 0 := by
    intro h0
    have := hQ.det_pos
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact lt_irrefl _ this
  have hudet : IsUnit u.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hdetJ ?_
    have := congrArg Matrix.det huJ
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  have huU : IsUnit u := (Matrix.isUnit_iff_isUnit_det u).mpr hudet
  refine ⟨huU.unit, ?_, ?_, ?_, ?_⟩
  · simpa using huJ
  · simpa using huX
  · intro v hv
    have hv' : X₂ᴴ *ᵥ (J *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec]; exact hv
    refine ⟨-(Dᴴ *ᵥ (J *ᵥ v)), ?_⟩
    simp only [IsUnit.unit_spec, hu, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_zero, Matrix.mulVec_neg]
    abel
  · simp only [IsUnit.unit_spec, huY, hY', Matrix.mul_assoc, hPiP, Matrix.mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtTensor
section
namespace GlobalTheory.RingHomTensorExtensionality

theorem ringHom_ext_tensor {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] {g h : TensorProduct R A B →+* C}
    (ha : ∀ a : A, g (a ⊗ₜ[R] (1 : B)) = h (a ⊗ₜ[R] (1 : B)))
    (hb : ∀ b : B, g ((1 : A) ⊗ₜ[R] b) = h ((1 : A) ⊗ₜ[R] b)) : g = h := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    have e : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, ha, hb]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.RingHomTensorExtensionality
end

