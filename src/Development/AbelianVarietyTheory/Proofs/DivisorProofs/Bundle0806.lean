module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffHasMultiplicities
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusGenCubical
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingLieMultiplicityZeroCharZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTLie

open GlobalTheory.EigenSplit GlobalTheory.TanMod GlobalTheory.DetCompare GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs

theorem eq_zero_of_mem_eigenSub_of_sum {O k N : Type} [CommRing O] [Field k] [AddCommGroup N] [Module k N]
    (ρ : O →+* Module.End k N) (σ : O →+* k) {κ : Type} (χ : κ → O →+* k) (hχ : ∀ i, χ i ≠ σ)
    (s : Finset κ) : ∀ (m : N) (y : κ → N), m ∈ eigenSub ρ σ → (∀ i, y i ∈ eigenSub ρ (χ i)) →
      m = ∑ i ∈ s, y i → m = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m y _ _ h; simpa using h
  | insert j s hj ih =>
    intro m y hm hy h
    obtain ⟨c, hc⟩ : ∃ c, χ j c ≠ σ c := by
      by_contra hcon
      push_neg at hcon
      exact hχ j (RingHom.ext hcon)
    let f : Module.End k N := ρ c - χ j c • LinearMap.id
    have hfm : f m = (σ c - χ j c) • m := by
      simp [f, mem_eigenSub.1 hm c, sub_smul]
    have hfy : ∀ i, f (y i) = (χ i c - χ j c) • y i := fun i => by
      simp [f, mem_eigenSub.1 (hy i) c, sub_smul]
    have h1 : (σ c - χ j c) • m = ∑ i ∈ s, (χ i c - χ j c) • y i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hfm, h, Finset.sum_insert hj, map_add (f := _), map_sum, hfy j, sub_self, zero_smul, zero_add]
      exact Finset.sum_congr rfl fun i _ => hfy i
    have h2 := ih ((σ c - χ j c) • m) (fun i => (χ i c - χ j c) • y i)
      (Submodule.smul_mem _ _ hm) (fun i => Submodule.smul_mem _ _ (hy i)) h1
    have hne : σ c - χ j c ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
    exact (smul_eq_zero.1 h2).resolve_left hne

theorem exists_ringHom_avoid {F : Type} [Field F] [NumberField F] [IsCMField F] (bar : 𝓞 F ≃+* 𝓞 F)
    (bar_eq : ∀ a : 𝓞 F, ((bar a : 𝓞 F) : F) = IsCMField.complexConj F (a : F))
    (ω : 𝓞 F) (tr nm : ℤ) (tr_eq : ω + bar ω = (tr : 𝓞 F)) (nm_eq : ω * bar ω = (nm : 𝓞 F))
    (disc_neg : tr ^ 2 - 4 * nm < 0)
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (ρ : k) (hρ : ρ ^ 2 - tr * ρ + nm = 0)
    (a : ℕ) (ha : 2 * a < Module.finrank ℚ F) (χ : Fin a → (𝓞 F →+* k)) :
    ∃ σ : 𝓞 F →+* k, σ ω = ρ ∧ ∀ i, χ i ≠ σ := by
  classical
  let cj : F →+* F := ((IsCMField.complexConj F : F ≃ₐ[maximalRealSubfield F] F) : F →+* F)
  have e1 : (ω : F) + ((bar ω : 𝓞 F) : F) = (tr : F) := by
    have := congrArg (fun z : 𝓞 F => (z : F)) tr_eq
    simpa using this
  have e2 : (ω : F) * ((bar ω : 𝓞 F) : F) = (nm : F) := by
    have := congrArg (fun z : 𝓞 F => (z : F)) nm_eq
    simpa using this
  have hcω : cj (ω : F) = (tr : F) - (ω : F) := by
    have : cj (ω : F) = ((bar ω : 𝓞 F) : F) := (bar_eq ω).symm
    rw [this]; linear_combination e1
  have hcc : ∀ z, cj (cj z) = z := fun z => IsCMField.complexConj_apply_apply F z
  have hroot : ∀ τ : F →+* k, τ ω ^ 2 - tr * τ ω + nm = 0 := by
    intro τ
    have h1 : (ω : F) ^ 2 - tr * (ω : F) + nm = 0 := by
      linear_combination (ω : F) * e1 - e2
    have := congrArg τ h1
    simpa using this
  have hne : ρ ≠ (tr : k) - ρ := by
    intro h
    have h3 : ((tr ^ 2 - 4 * nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (2 * ρ - tr) * h - 4 * hρ
    have h4 : tr ^ 2 - 4 * nm = 0 := by exact_mod_cast h3
    omega
  have hside : ∀ τ : F →+* k, τ ω ≠ ρ → τ ω = (tr : k) - ρ := by
    intro τ h
    have : (τ ω - ρ) * (τ ω - ((tr : k) - ρ)) = 0 := by
      linear_combination hroot τ - hρ
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd (sub_eq_zero.1 h') h
    · exact sub_eq_zero.1 h'
  have hconj : ∀ τ : F →+* k, (τ.comp cj) ω = (tr : k) - τ ω := by
    intro τ
    simp [hcω]
  let T := (Finset.univ : Finset (F →+* k)).filter (fun τ => τ ω = ρ)
  let Tc := (Finset.univ : Finset (F →+* k)).filter (fun τ => ¬ τ ω = ρ)
  have hcard : T.card = Tc.card := by
    refine Finset.card_nbij' (fun τ => τ.comp cj) (fun τ => τ.comp cj) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [T, Tc, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      rw [hconj, hτ]
      exact fun h => hne h.symm
    · intro τ hτ
      simp only [T, Tc, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      rw [hconj, hside τ hτ]; ring
    · intro τ _; ext z; simp [hcc]
    · intro τ _; ext z; simp [hcc]
  have htot : T.card + Tc.card = Module.finrank ℚ F := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, NumberField.Embeddings.card]
  by_contra hcon
  push_neg at hcon
  have hsub : T.image (fun τ => τ.comp (algebraMap (𝓞 F) F)) ⊆ Finset.univ.image χ := by
    intro σ hσ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hσ
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    obtain ⟨i, hi⟩ := hcon (τ.comp (algebraMap (𝓞 F) F)) (by simpa using hτ)
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hinj : Set.InjOn (fun τ : F →+* k => τ.comp (algebraMap (𝓞 F) F)) T := by
    intro τ _ τ' _ h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hle
  have hle2 := (Finset.card_image_le (s := (Finset.univ : Finset (Fin a))) (f := χ))
  rw [Finset.card_univ, Fintype.card_fin] at hle2
  omega

end GlobalTheory.HTLie

namespace GlobalTheory.HTLie

open GlobalTheory.EigenSplit GlobalTheory.TanMod GlobalTheory.DetCompare GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs

theorem exists_lieMult_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), 2 * D.a < Module.finrank ℚ D.F → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ σ : 𝓞 D.F →+* k, LieMult (o.act.toF D) x σ 0 := by
  intro p _ D R _ b N S s o ha k _ _ _ x β hx
  have hρ : β b.ρ ^ 2 - D.tr * β b.ρ + D.nm = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  obtain ⟨σ, hσω, hσ⟩ := exists_ringHom_avoid D.bar D.bar_eq D.ω D.tr D.nm D.tr_eq D.nm_eq D.disc_neg k
    (β b.ρ) hρ D.a ha (fun i => β.comp (b.t i))
  refine ⟨σ, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun w hw =>
    ⟨Fin.elim0, ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩, fun c _ => funext fun i => Fin.elim0 i⟩⟩
  rw [List.ofFn_zero, List.prod_nil]
  obtain ⟨w', hw', hwprod⟩ := o.lie k β x hx w ⟨hw.1, by
    have := hw.2 D.ω
    rw [hσω] at this
    exact this⟩
  have hlie : ∀ i, IsLieEigen (o.act.toF D) x (β.comp (b.t i)) (w' i) :=
    fun i => ⟨(hw' i 0).1, fun c => (hw' i c).2⟩
  obtain ⟨h1, h2⟩ := (isLieEigen_iff _ x σ w).1 hw
  choose g1 g2 using fun i => (isLieEigen_iff _ x _ (w' i)).1 (hlie i)
  have hm := (mem_eigenspace_iff _ x σ _).1 h2
  have hy := fun i => (mem_eigenspace_iff _ x _ _).1 (g2 i)
  have hsum : lieEquiv x ⟨w, h1⟩ = ∑ i ∈ Finset.univ, lieEquiv x ⟨w' i, g1 i⟩ := by
    apply TanSp.ext
    rw [TanSp.pt_sum]
    show w = ∏ i, w' i
    rw [hwprod, List.prod_ofFn]
  have h0 := eq_zero_of_mem_eigenSub_of_sum _ σ (fun i => β.comp (b.t i)) hσ Finset.univ _ _ hm hy hsum
  exact congrArg TanSp.pt h0

end GlobalTheory.HTLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubTriv
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EvenGenTorus

open TorusCube

theorem exists_ratio {S : Scheme.{0}} {H G : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj G] [IsCommMonObj G]
    (i : H ⟶ G) [IsMonHom i] (L : RigLB G) (c : CubicalStr G L)
    (τ : LB.Gen (LB.LinComb L.L (K := PUnit) (fun _ => i.left) (fun _ => 1))) (hτ : τ.IsGen) :
    ∃ w : Γ((H ⊗ H ⊗ H).left, ⊤)ˣ, ∀ (T : Over S) (x y u : T ⟶ H) (z : T.left)
      (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      ∀ v : (T ⟶ H) → (T.left.presheaf.stalk z)ˣ, (∀ a, v a = val τ a.left z J) →
      (v (x * y * u) * v x * v y * v u *
        (cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * v (x * y) * v (x * u) * v (y * u) * v 1)⁻¹).val =
        gs (𝟙 T.left) z ⊤ ((lift x (lift y u)).left.appTop.hom w.val) := by
  let p₀ := x3 H 0
  let p₁ := x3 H 1
  let p₂ := x3 H 2
  have P : ∀ p : G3 H ⟶ H, HasVal L.L (fun _ _ h => h (p.left ≫ i.left))
      (fun _ r z J => val τ (r ≫ p.left) z J) := fun p =>
    ⟨PUnit, inferInstance, _, _, LB.pullGen L.L (fun _ : PUnit => i.left) (fun _ => 1) τ p.left,
      DVR.pullGen_isGen _ _ _ _ hτ p.left, fun V _ k => by simp, fun Z r z J hJ => val_pull hJ _ _ _⟩
  let M := (lift (p₀ ≫ i) (lift (p₁ ≫ i) (p₂ ≫ i))).left
  have em : ∀ a b : G3 H ⟶ H, (a ≫ i) * (b ≫ i) = (a * b) ≫ i := fun a b => (MonObj.mul_comp _ _ _).symm
  have e1 : (1 : G3 H ⟶ G) = (1 : G3 H ⟶ H) ≫ i := (MonObj.one_comp _).symm
  have C : HasVal L.L (fun _ _ h => h ((p₀ * p₁ * p₂).left ≫ i.left) * (h ((p₀ * p₁).left ≫ i.left))⁻¹ *
      (h ((p₀ * p₂).left ≫ i.left))⁻¹ * (h ((p₁ * p₂).left ≫ i.left))⁻¹ * h (p₀.left ≫ i.left) *
        h (p₁.left ≫ i.left) * h (p₂.left ≫ i.left) * (h ((1 : G3 H ⟶ H).left ≫ i.left))⁻¹)
      (fun _ r z J => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t (r ≫ M) z J) :=
    ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ G (x3 G)) thε c.t M, DVR.pullGen_isGen _ _ _ _ c.isGen M,
      fun V _ h => by
        have := prod_cub (p₀ ≫ i) (p₁ ≫ i) (p₂ ≫ i) h
        rw [e1] at this
        simp only [em] at this
        simpa only [Over.comp_left] using this,
      fun Z r z J hJ => val_pull hJ _ _ _⟩
  obtain ⟨w, hw⟩ := (((((P (p₀ * p₁ * p₂)).mul (P p₀)).mul (P p₁)).mul (P p₂)).mul
    ((((C.mul (P (p₀ * p₁))).mul (P (p₀ * p₂))).mul (P (p₁ * p₂))).mul (P 1)).inv).exists_unit
    L.isLB (fun V _ k => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨w, fun T x y u z J hJ v hv => ?_⟩
  refine Eq.trans ?_ (hw _ (lift x (lift y u)).left z J hJ)
  have r₀ : lift x (lift y u) ≫ p₀ = x := by simp [p₀, x3]
  have r₁ : lift x (lift y u) ≫ p₁ = y := by simp [p₁, x3]
  have r₂ : lift x (lift y u) ≫ p₂ = u := by simp [p₂, x3]
  have hM : (lift x (lift y u)).left ≫ M = (lift (x ≫ i) (lift (y ≫ i) (u ≫ i))).left := by
    simp only [M, ← Over.comp_left, comp_lift, ← Category.assoc, r₀, r₁, r₂]
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, r₀, r₁, r₂, hv]
  rw [hM]
  rfl

theorem cube (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [IsCommMonObj G] (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G)
    [IsMonHom i] (L : RigLB G) (c : CubicalStr G L)
    (τ : LB.Gen (LB.LinComb L.L (K := PUnit) (fun _ => i.left) (fun _ => 1))) (hτ : τ.IsGen)
    (T : Over (Spec (CommRingCat.of k))) (x y u : T ⟶ splitTorus (Spec (CommRingCat.of k)) X) (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (hJ : Good L.L z J) :
    val τ (x * y * u).left z J * val τ x.left z J * val τ y.left z J * val τ u.left z J =
      cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * val τ (x * y).left z J * val τ (x * u).left z J *
        val τ (y * u).left z J * val τ (1 : T ⟶ splitTorus (Spec (CommRingCat.of k)) X).left z J := by
  obtain ⟨w, hw⟩ := exists_ratio i L c τ hτ
  have hT : TwoUniqueSums (X × X × X) := inferInstance
  have face : ∀ (Z : Over (Spec (CommRingCat.of k))) (a b d : Z ⟶ splitTorus (Spec (CommRingCat.of k)) X),
      (a = 1 ∨ b = 1 ∨ d = 1) → (lift a (lift b d)).left.appTop.hom w.val = 1 := by
    intro Z a b d h
    refine fn_ext fun q _ => ?_
    choose I hI using fun χ : Z.left ⟶ G.left => exists_chart L.isLB (χ q)
    have C := isCub_cubV c (show Good L.L q I from hI)
    rw [← hw Z a b d q I hI (fun a => val τ a.left q I) (fun _ => rfl), gs_eq _ q ⊤ trivial, map_one, map_one,
      Units.val_eq_one, mul_inv_eq_one]
    rcases h with rfl | rfl | rfl
    · rw [MonObj.one_comp, C.face]; simp only [_root_.one_mul, _root_.mul_one]; try ac_rfl
    · rw [MonObj.one_comp, C.face₂]; simp only [_root_.one_mul, _root_.mul_one]; try ac_rfl
    · rw [MonObj.one_comp, C.face₃]; simp only [_root_.one_mul, _root_.mul_one]; try ac_rfl
  have key := unit_eq_one k X w.val w.isUnit (face _ _ _ _ (Or.inr (Or.inl rfl))) (face _ _ _ _ (Or.inl rfl))
    (face _ _ _ _ (Or.inl rfl)) T x y u
  have := hw T x y u z J hJ _ (fun _ => rfl)
  rw [key, gs_eq _ z ⊤ trivial, map_one, map_one, Units.val_eq_one, mul_inv_eq_one] at this
  exact this

end GlobalTheory.EvenGenTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCosetsUnitIdelesCompletedOrder
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem exists_finset_cover_units : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∃ R : Finset (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) = 1) → ∃ r ∈ R, r⁻¹ * y ∈ hatOUnits c := by
  classical
  intro E _ _ c hc
  let U : Subgroup (Af E)ˣ := (PicFin.intR E).toSubmonoid.units
  have h1 : ((hatOUnits c).subgroupOf U).FiniteIndex := PicFin.finiteIndex_units hc
  have h2 : Finite (U ⧸ (hatOUnits c).subgroupOf U) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (U ⧸ (hatOUnits c).subgroupOf U)
  refine ⟨Finset.univ.image fun q : U ⧸ (hatOUnits c).subgroupOf U => (q.out : U).1, fun y hy => ?_⟩
  have hyU : y ∈ U := (Submonoid.mem_units_iff _ _).2
    ⟨fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hy v).le,
     fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (by rw [inv_coord, map_inv₀, hy v, inv_one])⟩
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨y, hyU⟩)), ?_⟩
  have h3 := (QuotientGroup.eq (s := (hatOUnits c).subgroupOf U)).1
    (QuotientGroup.out_eq' (QuotientGroup.mk ⟨y, hyU⟩ : U ⧸ (hatOUnits c).subgroupOf U))
  exact Subgroup.mem_subgroupOf.1 h3

end GlobalTheory.CMVal.Euler
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetDimDropClosed
section
set_option autoImplicit false

open TopologicalSpace

namespace GlobalTheory

theorem exists_finite_topologicalKrullDim_inter_add_one_le {T : Type} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] (Z : Set T) (hZ : IsClosed Z) :
    ∃ S : Set T, S.Finite ∧ ∀ C : Set T, IsClosed C → Disjoint S C →
      topologicalKrullDim (Z ∩ C : Set T) + 1 ≤ topologicalKrullDim Z := by
  obtain ⟨F, hF, hcl, hirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  choose g hg using fun t : F => QuasiSober.sober (hirr t.1 t.2) (hcl t.1 t.2)
  have := hF.to_subtype
  refine ⟨Set.range g, Set.finite_range g, fun C hC hd => ?_⟩
  refine topologicalKrullDim_add_one_le (hZ.inter hC) hZ ?_
  rintro x ⟨⟨t, ht, hxt⟩, -⟩
  exact ⟨g ⟨t, ht⟩, ⟨t, ht, (hg ⟨t, ht⟩).mem⟩, fun h => Set.disjoint_left.1 hd ⟨_, rfl⟩ h.2,
    (hg ⟨t, ht⟩).specializes hxt⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfMemLevel
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRankR

theorem exists_lift_of_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ) (κ' : GA D (Wc D i)), κ' ∈ levG (Wc D i) (R.βW i) (R.datWp i P) → ∃ g0 : P.H, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0.1 κ' ∧ levChi (Wc D i) (R.βW i) (R.datWp i P) κ' = ((P.chi g0 : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i P κ' hκ
  have hp : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ') ∈ P.H := hκ.2.2
  refine ⟨⟨_, hp⟩, ⟨hκ.1, hκ.2.1, rfl⟩, ?_⟩
  have h2 : ext1 (R.datWp i P).P.H (R.datWp i P).P.chi
      (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ')) = P.chi ⟨_, hp⟩ := extendOne_of_mem _ hp
  unfold levChi levFn
  rw [h2]
  have hs : (R.datWp i P).s = 0 := rfl
  have hQ : (R.datWp i P).Q = ∅ := rfl
  rw [hs, hQ]
  simp

end GlobalTheory.LevelRankR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfStrictCocycle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBGlue

variable {R : Type} [CommRing R] {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

abbrev UU (t : (Small i L)ᵒᵖ) : X.Opens := t.unop.1.1.1

theorem le_of_hom {t t' : (Small i L)ᵒᵖ} (a : t ⟶ t') : UU t' ≤ UU t := leOfHom a.unop

theorem hom_eq {t t' : (Small i L)ᵒᵖ} (a b : t ⟶ t') : a = b :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def homOf {t t' : (Small i L)ᵒᵖ} (h : UU t' ≤ UU t) : t ⟶ t' :=
  (homOfLE (show t'.unop ≤ t.unop from h)).op

variable (u : C1 (smallG i L ⋙ OAff s)) (hu : ∀ t t' a, IsUnit (u t t' a))

def uu (t t' : (Small i L)ᵒᵖ) (a : t ⟶ t') : Γ(X, UU t')ˣ := (hu t t' a).unit

variable {u hu}

theorem uu_comp (hm : mdef _ u = 0) {t t' t'' : (Small i L)ᵒᵖ} (a : t ⟶ t') (b : t' ⟶ t'') :
    res (le_of_hom b) (uu u hu t t' a) * uu u hu t' t'' b = uu u hu t t'' (a ≫ b) := by
  apply Units.ext
  have := congrFun (congrFun (congrFun (congrFun (congrFun hm t) t') t'') a) b
  exact sub_eq_zero.1 this

theorem gm_uu (hm : mdef _ u = 0) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) {t t' r : (Small i L)ᵒᵖ}
    (a : t ⟶ t') (b : t' ⟶ r) (hy : f y ∈ UU r) :
    gm f y (UU t') (uu u hu t t' a) =
      gm f y (UU r) (uu u hu t r (a ≫ b)) * (gm f y (UU r) (uu u hu t' r b))⁻¹ := by
  rw [← uu_comp hm a b, map_mul, gm_res f y _ hy, mul_inv_cancel_right]

theorem exists_g (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) (t t' : (Small i L)ᵒᵖ) :
    ∃ g : Γ(X, UU t ⊓ UU t')ˣ, ∀ p : (r : (Small i L)ᵒᵖ) × (t ⟶ r) × (t' ⟶ r),
      res (le_inf (le_of_hom p.2.1) (le_of_hom p.2.2)) g = uu u hu t p.1 p.2.1 * (uu u hu t' p.1 p.2.2)⁻¹ := by
  refine glue_unit _ (fun p : (r : (Small i L)ᵒᵖ) × (t ⟶ r) × (t' ⟶ r) ↦ UU p.1)
    (fun p ↦ le_inf (le_of_hom p.2.1) (le_of_hom p.2.2)) (fun x hx ↦ ?_) _ (fun p q x hx ↦ ?_)
  · obtain ⟨r, hr, hle⟩ := hB.cover x _ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r, homOf (hle.trans inf_le_left), homOf (hle.trans inf_le_right)⟩, hr⟩
  · obtain ⟨r, hr, hle⟩ := hB.cover x _ hx
    have c : p.1 ⟶ r := homOf (hle.trans inf_le_left)
    have d : q.1 ⟶ r := homOf (hle.trans inf_le_right)
    rw [map_mul, map_mul, map_inv, map_inv, gm_uu hm (𝟙 X) x p.2.1 c hr, gm_uu hm (𝟙 X) x p.2.2 c hr,
      gm_uu hm (𝟙 X) x q.2.1 d hr, gm_uu hm (𝟙 X) x q.2.2 d hr, hom_eq (q.2.1 ≫ d) (p.2.1 ≫ c),
      hom_eq (q.2.2 ≫ d) (p.2.2 ≫ c)]
    group

variable (u hu)

def glueLB (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) : LB X :=
  ⟨(Small i L)ᵒᵖ, UU, fun t t' ↦ Classical.choose (exists_g (hu := hu) hm hB t t')⟩

variable {u hu}

theorem gm_glue (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y)
    {t t' r : (Small i L)ᵒᵖ} (a : t ⟶ r) (b : t' ⟶ r) (hy : f y ∈ UU r) :
    gm f y (UU t ⊓ UU t') ((glueLB u hu hm hB).g t t') =
      gm f y (UU r) (uu u hu t r a) * (gm f y (UU r) (uu u hu t' r b))⁻¹ := by
  have := Classical.choose_spec (exists_g (hu := hu) hm hB t t') ⟨r, a, b⟩
  show gm f y _ (Classical.choose (exists_g (hu := hu) hm hB t t')) = _
  rw [← gm_res f y (le_inf (le_of_hom a) (le_of_hom b)) hy, this, map_mul, map_inv]

theorem isLB_glue (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) : (glueLB u hu hm hB).IsLB := {
  cover := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨r, hr, -⟩ := hB.cover x ⊤ trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨r, hr⟩
  g_self := fun (t : (Small i L)ᵒᵖ) ↦ by
    refine unit_ext fun x hx ↦ ?_
    obtain ⟨r, hr, hle⟩ := hB.cover x (UU t) hx
    rw [gm_res _ x _ hx, map_one]
    exact (gm_glue hm hB (𝟙 X) x (homOf hle) (homOf hle) hr).trans (mul_inv_cancel _)
  cocycle := fun (t t' t'' : (Small i L)ᵒᵖ) ↦ by
    refine unit_ext fun x hx ↦ ?_
    obtain ⟨r, hr, hle⟩ := hB.cover x (UU t ⊓ UU t' ⊓ UU t'') hx
    have a : t ⟶ r := homOf (hle.trans (inf_le_left.trans inf_le_left))
    have b : t' ⟶ r := homOf (hle.trans (inf_le_left.trans inf_le_right))
    have c : t'' ⟶ r := homOf (hle.trans inf_le_right)
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    refine (congrArg₂ (· * ·) (gm_glue hm hB (𝟙 X) x a b hr) (gm_glue hm hB (𝟙 X) x b c hr)).trans
      ((?_ : _ = _).trans (gm_glue hm hB (𝟙 X) x a c hr).symm)
    group }

theorem gm_lift (hl : IsLift s i L u) {t r : (Small i L)ᵒᵖ} (a : t ⟶ r) (y : X₀) (hy : i y ∈ UU r) :
    gm i y (UU r) (uu u hu t r a) = gm (𝟙 X₀) y _ (L.g t.unop.1.2 r.unop.1.2) := by
  have e := gm_pull (𝟙 X₀) i y (UU r) hy (uu u hu t r a)
  rw [Category.id_comp] at e
  have e' : pullU i (UU r) (uu u hu t r a) = res (Small.le_inf a) (L.g t.unop.1.2 r.unop.1.2) :=
    Units.ext (hl t r a)
  rw [← e, e', gm_res (𝟙 X₀) y _ hy]

def chart (hL : L.IsLB) (hl : IsLift s i L u) (hm : mdef _ u = 0) (hB : IsBasis (smallG i L)) :
    ChartPull ((glueLB u hu hm hB).pull i) L (𝟙 X₀) where
  idx J := (J PUnit.unit).unop.1.2
  le J y hy := (J PUnit.unit).unop.2 (mem_pull.1 hy)
  g y J J' hj hj' := by
    have hx : i y ∈ UU (J PUnit.unit) := mem_pull.1 hj
    have hx' : i y ∈ UU (J' PUnit.unit) := mem_pull.1 hj'
    obtain ⟨r, hr, hle⟩ := hB.cover (i y) (UU (J PUnit.unit) ⊓ UU (J' PUnit.unit)) ⟨hx, hx'⟩
    let t₁ : (Small i L)ᵒᵖ := J PUnit.unit
    let t₂ : (Small i L)ᵒᵖ := J' PUnit.unit
    have a : t₁ ⟶ r := homOf (hle.trans inf_le_left)
    have b : t₂ ⟶ r := homOf (hle.trans inf_le_right)
    have e := gm_pull_g (glueLB u hu hm hB) i (𝟙 X₀) y J J' hj hj'
    rw [Category.id_comp] at e
    refine e.trans ((gm_glue hm hB i y a b hr).trans ?_)
    rw [gm_lift hl a y hr, gm_lift hl b y hr]
    have hjr : (𝟙 X₀) y ∈ L.U r.unop.1.2 := r.unop.2 hr
    have hj₁ : (𝟙 X₀) y ∈ L.U (J PUnit.unit).unop.1.2 := (J PUnit.unit).unop.2 hx
    have hj₂ : (𝟙 X₀) y ∈ L.U (J' PUnit.unit).unop.1.2 := (J' PUnit.unit).unop.2 hx'
    rw [← gm_cocycle hL (𝟙 X₀) y hj₁ hj₂ hjr, mul_inv_cancel_right]

end GlobalTheory.LBGlue


open GlobalTheory.LBGlue in
theorem GlobalTheory.LBLift.exists_pic_of_strict_lift : ∀ (R : Type) [CommRing R] (X X₀ : Scheme.{0}) (s : X ⟶ Sp R)
    (i : X₀ ⟶ X) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsBasis (smallG i L) →
    IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) → mdef _ u = 0 →
    ∃ c : Pic X, GlobalTheory.CechPic.pull i c = cls L hL := by
  intro R _ X X₀ s i L hL u hB hl hu hm
  refine ⟨cls _ (isLB_glue (hu := hu) hm hB), ?_⟩
  rw [← cls_pull (isLB_glue (hu := hu) hm hB) i (pull_isLB (isLB_glue (hu := hu) hm hB) i)]
  exact (cls_eq_iff _ hL).2 (iso_of_chart hL (chart hL hl hm hB))
end
end

