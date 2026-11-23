module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAdicLimitMemAutomorphicSpace
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem spC_lim {A : Type} [CommRing A] (I : Ideal A) [IsPrecomplete I A] (x : ℕ → A)
    (h : ∀ k, x (k + 1) - x k ∈ I ^ k) : ∃ L, ∀ k, L - x k ∈ I ^ k := by
  have h1 : ∀ m n, m ≤ n → x n - x m ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem (Ideal.pow_le_pow_right hmn (h n)) ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance (f := x) (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (h1 m n hmn))
  refine ⟨L, fun k => ?_⟩
  have := hL k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  rw [← neg_sub]
  exact neg_mem this

private theorem spC_eq {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A] {x y : A}
    (h : ∀ k, x - y ∈ I ^ k) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact h k

theorem UpperTheory.exists_adic_limit_mem_automorphicSpace :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (a : ℕ → X.Fn A m), (∀ k, a k ∈ X.Sp τ θ U) → (∀ k, a (k + 1) - a k ∈ X.valIn A m k) → ∃ L ∈ X.Sp τ θ U, ∀ k, L - a k ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ U a ha hc
  have hv : ∀ (k : ℕ) (f : X.Fn A m), f ∈ X.valIn A m k ↔ ∀ g i, f g i ∈ maximalIdeal A ^ k := by
    intro k f
    simp [Frame.valIn, Submodule.mem_pi]
  choose L hL using fun g i => spC_lim (maximalIdeal A) (fun k => a k g i) fun k => (hv _ _).1 (hc k) g i
  have key : ∀ φ ψ : X.Fn A m →ₗ[A] X.Fn A m, (∀ k, ∀ f ∈ X.valIn A m k, φ f ∈ X.valIn A m k) →
      (∀ k, ∀ f ∈ X.valIn A m k, ψ f ∈ X.valIn A m k) → (∀ k, φ (a k) = ψ (a k)) → φ L = ψ L := by
    intro φ ψ h1 h2 h3
    funext g i
    refine spC_eq (maximalIdeal A) fun k => ?_
    have hk : L - a k ∈ X.valIn A m k := (hv _ _).2 fun g i => hL g i k
    have := sub_mem (h1 k _ hk) (h2 k _ hk)
    rw [map_sub, map_sub, h3 k, sub_sub_sub_cancel_right] at this
    exact (hv _ _).1 this g i
  have hrp : ∀ b k, ∀ f ∈ X.valIn A m k, X.rp A m b f ∈ X.valIn A m k := fun b k f hf =>
    (hv _ _).2 fun g i => (hv _ _).1 hf _ i
  refine ⟨L, ⟨⟨fun γ g => ?_, fun x hx => ?_, fun t => ?_, fun k => ?_⟩, fun u hu => ?_⟩,
    fun k => (hv _ _).2 fun g i => hL g i k⟩
  · funext i
    refine spC_eq (maximalIdeal A) fun k => ?_
    have := sub_mem (hL (X.glob γ * g) i k) (hL g i k)
    rwa [(ha k).1.1 γ g, sub_sub_sub_cancel_right] at this
  · exact key _ LinearMap.id (hrp x) (fun _ _ h => h) fun k => (ha k).1.2.1 x hx
  · exact key _ ((((θ t)⁻¹ : Aˣ) : A) • LinearMap.id) (hrp t) (fun _ _ h => Submodule.smul_mem _ _ h)
      fun k => (ha k).1.2.2.1 t
  · obtain ⟨c, h⟩ := (ha k).1.2.2.2 k
    refine ⟨c, fun y hy g i => ?_⟩
    have := add_mem (sub_mem (hL (g * (1, y)) i k) (hL g i k)) (h y hy g i)
    convert this using 1
    ring
  · refine key _ LinearMap.id (fun k f hf => (hv _ _).2 fun g i => ?_) (fun _ _ h => h) fun k => (ha k).2 u hu
    rw [Frame.ra_apply]
    simp only [mulVec, dotProduct]
    exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ((hv _ _).1 hf _ j)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFiniteIwahoriDoubleCosetRepresentatives
section
open IsLocalRing Matrix UpperTheory.V.Hi

private def repsRel {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (U : Subgroup X.Ub)
    (c : ℕ) : Setoid (Ga × Gp) where
  r g h := ∃ γ, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * h * ((u : Ga), b)
  iseqv :=
    { refl := fun g => ⟨1, 1, one_mem _, 1, one_mem _, by simp [Prod.mk_one_one]⟩
      symm := by
        rintro g h ⟨γ, u, hu, b, hb, rfl⟩
        refine ⟨γ⁻¹, u⁻¹, inv_mem hu, b⁻¹, inv_mem hb, ?_⟩
        have : (((u⁻¹ : X.Ub) : Ga), b⁻¹) = ((u : Ga), b)⁻¹ := rfl
        rw [this, map_inv]
        group
      trans := by
        rintro g h k ⟨γ, u, hu, b, hb, rfl⟩ ⟨γ', u', hu', b', hb', rfl⟩
        refine ⟨γ * γ', u' * u, mul_mem hu' hu, b' * b, mul_mem hb' hb, ?_⟩
        have : (((u' * u : X.Ub) : Ga), b' * b) = ((u' : Ga), b') * ((u : Ga), b) := rfl
        rw [this, map_mul]
        group }

theorem UpperTheory.exists_finite_iwahori_doubleCoset_representatives :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (U : Subgroup X.Ub), X.FinLevel U → ∀ c : ℕ, ∃ (N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) ∧ (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) := by
  intro Γ Ga Gp _ _ _ X U hU c
  obtain ⟨s, hs⟩ := hU
  haveI : Finite (X.I.Iw 0 ⧸ (X.I.Iw c).subgroupOf (X.I.Iw 0)) := Nat.finite_of_card_ne_zero (iwFin Gp X.I c).1
  haveI : Finite (Quotient (repsRel X U c)) := by
    refine Finite.of_surjective
      (fun p : s × (X.I.Iw 0 ⧸ (X.I.Iw c).subgroupOf (X.I.Iw 0)) =>
        Quotient.mk (repsRel X U c) ((p.1 : Ga × Gp) * (1, (p.2.out : Gp)))) ?_
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨γ, x, hx, u, hu, b, hb, rfl⟩ := hs g
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul ((X.I.Iw c).subgroupOf (X.I.Iw 0)) ⟨b, hb⟩
      refine ⟨(⟨x, hx⟩, ((⟨b, hb⟩ : X.I.Iw 0) : _ ⧸ _)), ?_⟩
      symm
      refine Quotient.sound ⟨γ, u, hu, ((m : X.I.Iw 0) : Gp)⁻¹, inv_mem (Subgroup.mem_subgroupOf.1 m.2), ?_⟩
      simp only [hm, Subgroup.coe_mul, mul_assoc, Prod.mk_mul_mk, one_mul, mul_inv_cancel, mul_one]
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Quotient (repsRel X U c))
  refine ⟨N, fun i => (e.symm i).out, fun g => ?_, fun i j γ u hu b hb h => ?_⟩
  · obtain ⟨γ, u, hu, b, hb, h⟩ := (repsRel X U c).symm (Quotient.mk_out (s := repsRel X U c) g)
    exact ⟨γ, e (Quotient.mk _ g), u, hu, b, hb, by simpa using h⟩
  · have h1 : Quotient.mk (repsRel X U c) (e.symm j).out = Quotient.mk (repsRel X U c) (e.symm i).out :=
      Quotient.sound ⟨γ, u, hu, b, hb, h⟩
    rw [Quotient.out_eq, Quotient.out_eq] at h1
    exact (e.symm.injective h1).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFreeLatticeSpanningOrdinaryPart
section
open IsLocalRing UpperTheory.V.Hi UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

theorem UpperTheory.exists_free_lattice_spanning_ordinary_part :
    ∀ (O Ω V ι : Type) [CommRing O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V] [Module O V] [IsScalarTower O Ω V] [Fintype ι] (C : Submodule Ω V) (T : Module.End Ω V) (ev : V →ₗ[Ω] (ι → Ω)), Function.Injective (algebraMap O Ω) → Set.BijOn ev C Set.univ → (∀ F ∈ C, T F ∈ C) → (∀ F ∈ C, (∀ i, ev F i ∈ mIm O Ω 0) → ∀ i, ev (T F) i ∈ mIm O Ω 0) → ∃ S : Submodule O V, Module.Free O S ∧ (⨆ μ : {μ : Ω // IsIntUnit O μ}, C ⊓ T.maxGenEigenspace μ.1) = Submodule.span Ω (S : Set V) ∧ (∀ F ∈ S, F ∈ C ∧ (∀ i, ev F i ∈ mIm O Ω 0) ∧ ∀ k : ℕ, ∃ n : ℕ, ∀ i, ev ((T ^ (n + 1)) F - F) i ∈ mIm O Ω k) ∧ ∀ F ∈ C, (∀ i, ev F i ∈ mIm O Ω 0) → ∃ F' ∈ S, ∀ k : ℕ, ∃ J : ℕ, ∀ j, J ≤ j → ∀ i, ev ((T ^ j.factorial) F - F') i ∈ mIm O Ω k := by
  intro O Ω V ι _ _ _ _ _ _ _ _ _ _ C T ev hinj hbij hTC hint
  haveI : IsAdicComplete (maximalIdeal O) O := IsCNL.complete
  haveI : Finite (ResidueField O) := IsCNL.finite
  obtain ⟨hadm, hfin⟩ := ordAdm_maximalIdeal_and_finite_quotients (R := O) (M := ι → O)
  have hfin' := hfin ‹_›
  set A := algebraMap O Ω with hA
  let evC : C →ₗ[Ω] (ι → Ω) := ev ∘ₗ C.subtype
  have hevC : Function.Bijective evC := by
    refine ⟨fun x y hxy => Subtype.ext (hbij.injOn x.2 y.2 hxy), fun w => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn (Set.mem_univ w)
    exact ⟨⟨x, hx⟩, rfl⟩
  let e := LinearEquiv.ofBijective evC hevC
  let g : (ι → Ω) →ₗ[Ω] V := C.subtype ∘ₗ e.symm.toLinearMap
  have hgC : ∀ w, g w ∈ C := fun w => (e.symm w).2
  have hevg : ∀ w, ev (g w) = w := fun w => e.apply_symm_apply w
  have hgev : ∀ F ∈ C, g (ev F) = F := fun F hF => by
    have : e ⟨F, hF⟩ = ev F := rfl
    show ((e.symm (ev F) : C) : V) = F
    rw [← this, e.symm_apply_apply]
  have hginj : Function.Injective g := fun a b h => by rw [← hevg a, ← hevg b, h]
  let T' : Module.End Ω (ι → Ω) := ev ∘ₗ T ∘ₗ g
  have hgT : ∀ w, g (T' w) = T (g w) := fun w => hgev _ (hTC _ (hgC w))
  let jL : (ι → O) →ₗ[O] (ι → Ω) := LinearMap.pi (fun i => (Algebra.linearMap O Ω) ∘ₗ LinearMap.proj i)
  have hjL : ∀ v i, jL v i = A (v i) := fun v i => rfl
  have hjinj : Function.Injective jL := fun v w h => funext fun i => hinj (by rw [← hjL, ← hjL, h])
  have hmem0 : ∀ x : O, A x ∈ mIm O Ω 0 := fun x => mem_mIm.2 ⟨x, by simp, rfl⟩
  have hint' : ∀ v : ι → O, ∀ i, ∃ x : O, A x = T' (jL v) i := by
    intro v i
    have h1 : ∀ i, ev (g (jL v)) i ∈ mIm O Ω 0 := fun i => by rw [hevg]; exact hmem0 _
    obtain ⟨x, -, hx⟩ := mem_mIm.1 (hint _ (hgC _) h1 i)
    exact ⟨x, hx⟩
  choose f0 hf0 using hint'
  let T₀ : Module.End O (ι → O) :=
    { toFun := f0
      map_add' := fun v w => funext fun i => hinj (by
        simp only [Pi.add_apply, map_add (f := _), hf0])
      map_smul' := fun c v => funext fun i => hinj (by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, hf0, RingHom.id_apply]
        rw [map_smul, ← algebraMap_smul Ω c (jL v), map_smul, Pi.smul_apply, smul_eq_mul]) }
  have hT₀ : ∀ v, T' (jL v) = jL (T₀ v) := fun v => funext fun i => (hf0 v i).symm
  have key := UpperTheory.span_ordinaryPart_eq_sup_unit_generalized_eigenspaces O Ω ι T₀ T' (fun v => hT₀ v)
  let L : (ι → O) →ₗ[O] V := (g.restrictScalars O) ∘ₗ jL
  have hLinj : Function.Injective L := hginj.comp hjinj
  have hpow : ∀ m w, g ((T' ^ m) w) = (T ^ m) (g w) := pow_intertwine (U := T') (U' := T) (f := g) hgT
  have hpow0 : ∀ m u, jL ((T₀ ^ m) u) = (T' ^ m) (jL u) :=
    pow_intertwine (U := T₀) (U' := T') (f := jL) (fun u => (hT₀ u).symm)
  have hcoord : ∀ k (x : ι → O), x ∈ maximalIdeal O ^ k • (⊤ : Submodule O (ι → O)) → ∀ i, x i ∈ maximalIdeal O ^ k := by
    intro k x hx i
    have := map_mem_smul_top (LinearMap.proj (R := O) (φ := fun _ : ι => O) i) _ hx
    simpa using this
  refine ⟨(ordPart T₀).map L, ?_, ?_, ?_, ?_⟩
  · haveI := (ordProjective hadm T₀).1 inferInstance
    haveI := (ordProjective hadm T₀).2 inferInstance
    haveI : Module.Free O (ordPart T₀) := Module.free_of_flat_of_isLocalRing
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective L hLinj _)
  · have key' : (⨆ μ : {μ : Ω // IsIntUnit O μ}, T'.maxGenEigenspace μ.1) =
        Submodule.span Ω (jL '' (ordPart T₀ : Set (ι → O))) := key
    have hspan : Submodule.span Ω (((ordPart T₀).map L : Submodule O V) : Set V) =
        (Submodule.span Ω (jL '' (ordPart T₀ : Set (ι → O)))).map g := by
      rw [← Submodule.span_image, Submodule.map_coe, Set.image_image]
      rfl
    have heig : ∀ μ : Ω, C ⊓ T.maxGenEigenspace μ = (T'.maxGenEigenspace μ).map g := by
      intro μ
      have hpowμ : ∀ (k : ℕ) (w : ι → Ω), g (((T' - μ • (1 : Module.End Ω (ι → Ω))) ^ k) w) =
          ((T - μ • (1 : Module.End Ω V)) ^ k) (g w) :=
        pow_intertwine (U := T' - μ • 1) (U' := T - μ • 1) (f := g) (fun w => by simp [hgT])
      ext x
      constructor
      · rintro ⟨hxC, hx⟩
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
        refine ⟨ev x, (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, hginj ?_⟩, hgev x hxC⟩
        rw [hpowμ, hgev x hxC, hk, map_zero]
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hw
        exact ⟨hgC w, (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [← hpowμ, hk, map_zero]⟩⟩
    rw [hspan, ← key', Submodule.map_iSup]
    exact iSup_congr fun μ => heig μ.1
  · rintro F ⟨v, hv, rfl⟩
    refine ⟨hgC _, fun i => ?_, fun k => ?_⟩
    · show ev (g (jL v)) i ∈ _
      rw [hevg]
      exact hmem0 _
    · obtain ⟨n, hn⟩ := (ordPer hadm hfin' T₀ v).1 hv k
      refine ⟨n, fun i => ?_⟩
      show ev ((T ^ (n + 1)) (g (jL v)) - g (jL v)) i ∈ _
      rw [← hpow, ← hpow0, ← map_sub, hevg, ← map_sub, hjL]
      exact mem_mIm.2 ⟨_, hcoord _ _ hn i, rfl⟩
  · intro F hF hFi
    choose v _ hv using fun i => mem_mIm.1 (hFi i)
    have hFv : F = g (jL v) := by
      rw [← hgev F hF]
      congr 1
      funext i
      exact (hv i).symm
    refine ⟨L (ordProj (maximalIdeal O) T₀ v), ⟨_, ?_, rfl⟩, fun k => ?_⟩
    · rw [← (ordExists hadm T₀).2.1]
      exact LinearMap.mem_range_self _ _
    · obtain ⟨N, hN⟩ := (ordFactLim hadm hfin' T₀ _).2 rfl k
      refine ⟨N, fun j hj i => ?_⟩
      rw [hFv]
      show ev ((T ^ j.factorial) (g (jL v)) - g (jL (ordProj _ T₀ v))) i ∈ _
      rw [← hpow, ← hpow0, ← map_sub, hevg, ← map_sub, hjL]
      exact mem_mIm.2 ⟨_, hcoord _ _ (hN j hj v) i, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIwahoriTorusProjection
section
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem torus_uniq {G : Type} [Group G] (I : Iwa G) {y y' x x' : G} {t t' : I.T} (hy : y ∈ I.Nm 0)
    (hy' : y' ∈ I.Nm 0) (hx : x ∈ I.N) (hx' : x' ∈ I.N) (h : y * t * x = y' * t' * x') : t' = t := by
  have h1 : x = (t : G)⁻¹ * y⁻¹ * (y' * t' * x') := by rw [← h]; group
  have h0 := (I.uniq (x * x'⁻¹) (I.N_le (mul_mem hx (inv_mem hx'))) ((t' : G)⁻¹ * t)
    (I.T_le (mul_mem (inv_mem t'.2) t.2)) ((t : G)⁻¹ * (y'⁻¹ * y) * (t : G)⁻¹⁻¹)
    (I.T_Nm 0 _ (inv_mem t.2) _ (mul_mem (inv_mem hy') hy)) (by rw [h1]; group)).2
  exact Subtype.ext (inv_mul_eq_one.1 h0)

private theorem torus_ex {G : Type} [Group G] (I : Iwa G) {b : G} (hb : b ∈ I.Iw 0) :
    ∃ t : I.T, ∃ y ∈ I.Nm 0, ∃ x ∈ I.N, b = y * t * x := by
  obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I 0 b⁻¹).1.1 (inv_mem hb)
  refine ⟨⟨t⁻¹, inv_mem ht⟩, y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, ?_⟩
  rw [← inv_inv b, h]
  group

private theorem torus_fn {G : Type} [Group G] (I : Iwa G) :
    ∃ tt : G → I.T, ∀ (t : I.T), ∀ y ∈ I.Nm 0, ∀ x ∈ I.N, tt (y * t * x) = t := by
  classical
  refine ⟨fun b => if h : ∃ t : I.T, ∃ y ∈ I.Nm 0, ∃ x ∈ I.N, b = y * t * x then h.choose else 1, ?_⟩
  intro t y hy x hx
  have h : ∃ t' : I.T, ∃ y' ∈ I.Nm 0, ∃ x' ∈ I.N, y * t * x = y' * t' * x' := ⟨t, y, hy, x, hx, rfl⟩
  simp only [dif_pos h]
  obtain ⟨y', hy', x', hx', e⟩ := h.choose_spec
  exact torus_uniq I hy hy' hx hx' e

theorem UpperTheory.exists_iwahori_torus_projection :
    ∀ (G : Type) [Group G] (I : Iwa G), ∃ tt : G → I.T, tt 1 = 1 ∧ ∀ b ∈ I.Iw 0, (∀ s : I.T, tt (s * b) = s * tt b ∧ tt (b * s) = tt b * s) ∧ (∀ x ∈ I.N, tt (b * x) = tt b) ∧ ∀ c, ∀ y ∈ I.Nm c, ∃ s : I.T, (s : G) ∈ I.Tc c ∧ tt (b * y) = tt b * s := by
  intro G _ I
  obtain ⟨tt, htt⟩ := torus_fn I
  refine ⟨tt, by simpa using htt 1 1 (one_mem _) 1 (one_mem _), fun b hb => ?_⟩
  obtain ⟨t, y, hy, x, hx, rfl⟩ := torus_ex I hb
  rw [htt t y hy x hx]
  refine ⟨fun s => ⟨?_, ?_⟩, fun x' hx' => ?_, fun c y' hy' => ?_⟩
  · rw [← htt (s * t) _ (I.T_Nm 0 s s.2 y hy) x hx]
    congr 1
    rw [Subgroup.coe_mul]
    group
  · rw [← htt (t * s) y hy _ (I.T_N _ (inv_mem s.2) x hx)]
    congr 1
    rw [Subgroup.coe_mul]
    group
  · rw [mul_assoc]
    exact htt t y hy _ (mul_mem hx hx')
  · obtain ⟨x2, hx2, s, hs, y2, hy2, h⟩ := I.swap c y'⁻¹ (inv_mem hy') x⁻¹ (inv_mem hx)
    refine ⟨⟨s⁻¹, inv_mem (I.Tc_le c hs)⟩, inv_mem hs, ?_⟩
    rw [← htt (t * ⟨s⁻¹, inv_mem (I.Tc_le c hs)⟩) _
      (mul_mem hy (I.T_Nm 0 t t.2 _ (inv_mem (I.Nm_anti (Nat.zero_le c) hy2)))) _ (inv_mem hx2)]
    congr 1
    have e : x * y' = (x2 * s * y2)⁻¹ := by rw [← h]; group
    rw [mul_assoc, e, Subgroup.coe_mul]
    group
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLinearSectionAutomorphicFunctionsOfFree
section
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_linear_section_automorphicFunctions_of_free :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub), X.Free τ θ U → ∀ (c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) → ∀ tt : Gp → X.I.T, (∀ b ∈ X.I.Iw 0, ∀ s : X.I.T, tt (s * b) = s * tt b) → ∃ s : (Fin N × Fin m → A) →ₗ[A] X.Fn A m, ∀ v γ i, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, s v (X.glob γ * x i * ((u : Ga), b)) = (((θ (tt b))⁻¹ : Aˣ) : A) • ((τ u⁻¹ : Matrix (Fin m) (Fin m) A) *ᵥ fun j => v (i, j)) := by
  intro Γ Ga Gp _ _ _ X A _ m τ θ U hF c N x hcov hsep tt htt
  choose γ0 i0 u0 hu0 b0 hb0 hg using hcov
  have hle : X.I.Iw c ≤ X.I.Iw 0 := sup_le_sup_left (X.I.Nm_anti (Nat.zero_le c)) _
  refine ⟨{ toFun := fun v g => (((θ (tt (b0 g)))⁻¹ : Aˣ) : A) •
              ((τ (u0 g)⁻¹ : Matrix (Fin m) (Fin m) A) *ᵥ fun j => v (i0 g, j))
            map_add' := fun v w => ?_
            map_smul' := fun a v => ?_ }, fun v γ i u hu b hb => ?_⟩
  · funext g
    rw [Pi.add_apply, ← smul_add, ← mulVec_add]
    rfl
  · funext g
    rw [Pi.smul_apply, RingHom.id_apply, smul_comm a, ← mulVec_smul _ a]
    rfl
  · have h := hg (X.glob γ * x i * ((u : Ga), b))
    have hu1 := hu0 (X.glob γ * x i * ((u : Ga), b))
    have hb1 := hb0 (X.glob γ * x i * ((u : Ga), b))
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    generalize γ0 (X.glob γ * x i * ((u : Ga), b)) = γ1 at h
    generalize i0 (X.glob γ * x i * ((u : Ga), b)) = i1 at h ⊢
    generalize u0 (X.glob γ * x i * ((u : Ga), b)) = u1 at h hu1 ⊢
    generalize b0 (X.glob γ * x i * ((u : Ga), b)) = b1 at h hb1 ⊢
    have hw : ((((u1 * u⁻¹ : X.Ub) : Ga), b1 * b⁻¹) : Ga × Gp) = ((u1 : Ga), b1) * ((u : Ga), b)⁻¹ := rfl
    have hwU : u1 * u⁻¹ ∈ U := mul_mem hu1 (inv_mem hu)
    have hwI : b1 * b⁻¹ ∈ X.I.Iw c := mul_mem hb1 (inv_mem hb)
    have hi : i1 = i := by
      refine hsep i1 i (γ⁻¹ * γ1) _ hwU _ hwI ?_
      rw [hw, map_mul, map_inv, ← mul_assoc, mul_assoc (X.glob γ)⁻¹, mul_assoc (X.glob γ)⁻¹, ← h]
      group
    subst hi
    obtain ⟨-, hs, he⟩ := hF (x i1) (γ1⁻¹ * γ) _ hwU _ (hle hwI) (by
      rw [hw, map_mul, map_inv, mul_assoc, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← h]
      group)
    have ht : tt b1 = ⟨b1 * b⁻¹, hs⟩ * tt b := by
      rw [← htt b (hle hb) ⟨b1 * b⁻¹, hs⟩]
      simp
    have hτ : (τ u1⁻¹ : Matrix (Fin m) (Fin m) A) =
        (θ ⟨b1 * b⁻¹, hs⟩ : A) • (τ u⁻¹ : Matrix (Fin m) (Fin m) A) := by
      have e : u⁻¹ = u1⁻¹ * (u1 * u⁻¹) := by group
      rw [e, map_mul, Units.val_mul, ← Matrix.mul_smul, he, Matrix.mul_one]
    rw [ht, hτ, map_mul, smul_mulVec, smul_smul, ← Units.val_mul]
    congr 2
    rw [mul_inv, mul_right_comm, inv_mul_cancel, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsStarFixedRotationBasisOfCharpoly
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private theorem star_fixed_eq {K : Type} [Field K] [CharZero K] (Δ : K) (z : Lsq K Δ) (h : star z = z) :
    algebraMap K (Lsq K Δ) z.re = z := by
  have him : -z.im = z.im := by simpa using congrArg QuadraticAlgebra.im h
  have h0 : z.im = 0 := by
    have h2 : (2 : K) * z.im = 0 := by linear_combination -him
    simpa using h2
  ext
  · simp
  · simp [h0]

private theorem star_algebraMap {K : Type} [Field K] (Δ : K) (x : K) :
    star (algebraMap K (Lsq K Δ) x) = algebraMap K (Lsq K Δ) x := by
  ext <;> simp

private theorem map_star_mulVec {R : Type} [CommRing R] [StarRing R] (A : Matrix (Fin 3) (Fin 3) R) (y : Fin 3 → R) :
    star (A *ᵥ y) = A.map star *ᵥ star y := by
  funext i
  exact RingHom.map_mulVec (starRingEnd R) A y i

private theorem conj_fixed {R : Type} [CommRing R] [StarRing R] (B N Q : Matrix (Fin 3) (Fin 3) R)
    (hB : B * B.map star = 1) (hNB : N * B = B * N.map star) (hQu : IsUnit Q.det) (hQ : B * Q.map star = Q) :
    (Q⁻¹ * N * Q).map star = Q⁻¹ * N * Q := by
  have hRQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQu
  have hmul : ∀ X Y : Matrix (Fin 3) (Fin 3) R, (X * Y).map star = X.map star * Y.map star :=
    fun X Y => Matrix.map_mul (f := starRingEnd R)
  have hone : (1 : Matrix (Fin 3) (Fin 3) R).map star = 1 :=
    Matrix.map_one (starRingEnd R) (map_zero _) (map_one _)
  have hBs : B.map star * B = 1 := mul_eq_one_comm.1 hB
  have hRsQs : (Q⁻¹).map star * Q.map star = 1 := by rw [← hmul, hRQ, hone]
  have hQsRs : Q.map star * (Q⁻¹).map star = 1 := mul_eq_one_comm.1 hRsQs
  have hRB : Q⁻¹ * B = (Q⁻¹).map star := by
    calc Q⁻¹ * B = Q⁻¹ * B * (Q.map star * (Q⁻¹).map star) := by rw [hQsRs, mul_one]
      _ = Q⁻¹ * (B * Q.map star) * (Q⁻¹).map star := by simp only [Matrix.mul_assoc]
      _ = (Q⁻¹).map star := by rw [hQ, hRQ, one_mul]
  have hNs : N.map star = B.map star * N * B := by
    rw [Matrix.mul_assoc, hNB, ← Matrix.mul_assoc, hBs, one_mul]
  rw [hmul, hmul, hNs]
  calc (Q⁻¹).map star * (B.map star * N * B) * Q.map star
      = (Q⁻¹).map star * B.map star * N * (B * Q.map star) := by simp only [Matrix.mul_assoc]
    _ = (Q⁻¹ * B) * B.map star * N * Q := by rw [hQ, hRB]
    _ = Q⁻¹ * (B * B.map star) * N * Q := by simp only [Matrix.mul_assoc]
    _ = Q⁻¹ * N * Q := by rw [hB, Matrix.mul_one]

private theorem det_unit {K R : Type} [Field K] [CommRing R] (A : K →+* R) (Q : Matrix (Fin 3) (Fin 3) R)
    (hQu : IsUnit Q.det) (a b c : Fin 3 → K) (hdet : (Matrix.of ![a, b, c]).det ≠ 0) :
    IsUnit (Matrix.of ![Q *ᵥ (A ∘ a), Q *ᵥ (A ∘ b), Q *ᵥ (A ∘ c)]).det := by
  have hfac : Matrix.of ![Q *ᵥ (A ∘ a), Q *ᵥ (A ∘ b), Q *ᵥ (A ∘ c)] =
      (Matrix.of ![a, b, c]).map A * Qᵀ := by
    ext i j
    fin_cases i <;> simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [hfac, Matrix.det_mul, Matrix.det_transpose]
  refine IsUnit.mul ?_ hQu
  have : ((Matrix.of ![a, b, c]).map A).det = A (Matrix.of ![a, b, c]).det :=
    (RingHom.map_det A _).symm
  rw [this]
  exact (isUnit_iff_ne_zero.2 hdet).map A

private theorem charpoly_conj' {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (Q N : Matrix n n R)
    (hRQ : Q⁻¹ * Q = 1) (hQR : Q * Q⁻¹ = 1) : (Q⁻¹ * N * Q).charpoly = N.charpoly := by
  have := Matrix.charpoly_units_conj' (⟨Q, Q⁻¹, hQR, hRQ⟩ : (Matrix n n R)ˣ) N
  simpa using this

private theorem core {K R : Type} [Field K] [CommRing R] [StarRing R] (A : K →+* R)
    (hAinj : Function.Injective A) (hfix : ∀ z : R, star z = z → ∃ x, A x = z)
    (hst : ∀ x, star (A x) = A x) (τ : K)
    (hI : ∀ M : Matrix (Fin 3) (Fin 3) K,
      M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1) →
      ∃ e v : Fin 3 → K, M *ᵥ e = e ∧ M *ᵥ (M *ᵥ v) = τ • (M *ᵥ v) - v ∧ (Matrix.of ![e, v, M *ᵥ v]).det ≠ 0)
    (B N Q : Matrix (Fin 3) (Fin 3) R) (hB : B * B.map star = 1) (hNB : N * B = B * N.map star)
    (hchar : N.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C (A τ) * Polynomial.X + 1))
    (hQu : IsUnit Q.det) (hQ : B * Q.map star = Q) :
    ∃ e v : Fin 3 → R, B *ᵥ star e = e ∧ B *ᵥ star v = v ∧ N *ᵥ e = e ∧
      N *ᵥ (N *ᵥ v) = A τ • (N *ᵥ v) - v ∧ IsUnit (Matrix.of ![e, v, N *ᵥ v]).det := by
  have hRQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQu
  have hQR : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQu
  have hfx := conj_fixed B N Q hB hNB hQu hQ
  have hex : ∀ i j, ∃ x, A x = (Q⁻¹ * N * Q) i j := fun i j =>
    hfix _ (congrFun (congrFun hfx i) j)
  choose m hm using hex
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) K, M.map A = Q⁻¹ * N * Q := by
    refine ⟨Matrix.of m, ?_⟩
    ext i j
    exact hm i j
  have hcp : (Q⁻¹ * N * Q).charpoly = N.charpoly := charpoly_conj' Q N hRQ hQR
  have hMc : M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1) := by
    apply Polynomial.map_injective A hAinj
    rw [← Matrix.charpoly_map, hM, hcp, hchar]
    simp
  obtain ⟨e₀, v₀, he, hv, hdet⟩ := hI M hMc
  have hL : ∀ x : Fin 3 → K, (Q⁻¹ * N * Q) *ᵥ (A ∘ x) = A ∘ (M *ᵥ x) := by
    intro x
    funext i
    rw [← hM]
    exact (RingHom.map_mulVec A M x i).symm
  have hN : ∀ x : Fin 3 → K, N *ᵥ (Q *ᵥ (A ∘ x)) = Q *ᵥ (A ∘ (M *ᵥ x)) := by
    intro x
    rw [← hL, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQR, one_mul]
  have hS : ∀ x : Fin 3 → K, B *ᵥ star (Q *ᵥ (A ∘ x)) = Q *ᵥ (A ∘ x) := by
    intro x
    have : star (A ∘ x) = A ∘ x := by
      funext i
      exact hst (x i)
    rw [map_star_mulVec, this, Matrix.mulVec_mulVec, hQ]
  refine ⟨Q *ᵥ (A ∘ e₀), Q *ᵥ (A ∘ v₀), hS _, hS _, ?_, ?_, ?_⟩
  · rw [hN, he]
  · rw [hN, hN, hv]
    have : A ∘ (τ • (M *ᵥ v₀) - v₀) = A τ • (A ∘ (M *ᵥ v₀)) - A ∘ v₀ := by
      funext i
      simp
    rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul]
  · rw [hN]
    exact det_unit A Q hQu _ _ _ hdet

theorem UpperTheory.exists_star_fixed_rotation_basis_of_charpoly :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ : K), Δ ≠ 0 → τ ^ 2 - 4 ≠ 0 → ∀ B N : Matrix (Fin 3) (Fin 3) (Lsq K Δ),
        B * B.map star = 1 → N * B = B * N.map star →
        N.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C (algebraMap K (Lsq K Δ) τ) * Polynomial.X + 1) →
        ∃ e v : Fin 3 → Lsq K Δ, B *ᵥ star e = e ∧ B *ᵥ star v = v ∧ N *ᵥ e = e ∧
          N *ᵥ (N *ᵥ v) = algebraMap K (Lsq K Δ) τ • (N *ᵥ v) - v ∧ IsUnit (Matrix.of ![e, v, N *ᵥ v]).det := by
  intro K _ _ Δ τ hΔ hτ B N hB hNB hchar
  obtain ⟨Q, hQu, hQ⟩ := UpperTheory.exists_isUnit_det_mul_map_star_eq_of_unitary K Δ hΔ B hB
  refine core (algebraMap K (Lsq K Δ)) ?_ (fun z hz => ⟨z.re, star_fixed_eq Δ z hz⟩) (star_algebraMap Δ) τ
    (UpperTheory.exists_fixed_rotation_basis_of_charpoly K τ hτ) B N Q hB hNB hchar hQu hQ
  intro x y h
  simpa using congrArg QuadraticAlgebra.re h
end

