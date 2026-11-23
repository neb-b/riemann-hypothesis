module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeRingActionIffEndomorphismRelations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActRel

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def prodPow {r : ℕ} (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ) : A ⟶ A := ∏ k, f k ^ c k

theorem prodPow_add {r : ℕ} (f : Fin r → (A ⟶ A)) (c d : Fin r → ℤ) :
    prodPow f (c + d) = prodPow f c * prodPow f d := by
  simp [prodPow, zpow_add, Finset.prod_mul_distrib]

theorem prodPow_zero {r : ℕ} (f : Fin r → (A ⟶ A)) : prodPow f 0 = 1 := by
  simp [prodPow]

theorem prodPow_zsmul {r : ℕ} (f : Fin r → (A ⟶ A)) (n : ℤ) (c : Fin r → ℤ) :
    prodPow f (n • c) = prodPow f c ^ n := by
  simp [prodPow, zpow_mul', Finset.prod_zpow]

theorem prodPow_single {r : ℕ} (f : Fin r → (A ⟶ A)) (k : Fin r) : prodPow f (Pi.single k 1) = f k := by
  unfold prodPow
  rw [Finset.prod_eq_single k]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

def prodPowHom {r : ℕ} (f : Fin r → (A ⟶ A)) : Multiplicative (Fin r → ℤ) →* (A ⟶ A) :=
  MonoidHom.mk' (fun c => prodPow f c.toAdd) (fun c d => prodPow_add f c.toAdd d.toAdd)

theorem prodPow_sum {r : ℕ} (f : Fin r → (A ⟶ A)) {J : Type} (s : Finset J) (g : J → Fin r → ℤ) :
    prodPow f (∑ i ∈ s, g i) = ∏ i ∈ s, prodPow f (g i) := by
  have := map_prod (prodPowHom f) (fun i => Multiplicative.ofAdd (g i)) s
  rw [← ofAdd_sum] at this
  exact this

def precompHom (h : A ⟶ A) : (A ⟶ A) →* (A ⟶ A) :=
  MonoidHom.mk' (fun x => h ≫ x) (fun x y => MonObj.comp_mul h x y)

def postcompHom (h : A ⟶ A) [IsMonHom h] : (A ⟶ A) →* (A ⟶ A) :=
  MonoidHom.mk' (fun x => x ≫ h) (fun x y => MonObj.mul_comp x y h)

end GlobalTheory.ActRel

namespace GlobalTheory.ActRel

theorem prodPow_comp {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (f : Fin r → (A ⟶ A))
    (hf : ∀ k, IsMonHom (f k)) (cm : Fin r → Fin r → Fin r → ℤ) (hm : ∀ i j, f i ≫ f j = prodPow f (cm i j))
    (c d : Fin r → ℤ) :
    prodPow f c ≫ prodPow f d = prodPow f (∑ k, ∑ l, (c k * d l) • cm k l) := by
  haveI : IsMonHom (prodPow f d) := isMonHom_prodPow f hf d
  have h1 : prodPow f c ≫ prodPow f d = ∏ k, (f k ≫ prodPow f d) ^ c k := by
    have := map_prod (postcompHom (prodPow f d)) (fun k => f k ^ c k) Finset.univ
    refine this.trans (Finset.prod_congr rfl fun k _ => ?_)
    show (f k ^ c k) ≫ prodPow f d = _
    exact GrpObj.zpow_comp (f k) (c k) (prodPow f d)
  have h2 : ∀ k, f k ≫ prodPow f d = ∏ l, prodPow f (cm k l) ^ d l := by
    intro k
    have := map_prod (precompHom (f k)) (fun l => f l ^ d l) Finset.univ
    refine this.trans (Finset.prod_congr rfl fun l _ => ?_)
    show f k ≫ f l ^ d l = _
    rw [GrpObj.comp_zpow, hm]
  rw [h1, prodPow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h2, prodPow_sum, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [prodPow_zsmul, ← zpow_mul, mul_comm]

theorem ringAct_iff_relations : ∀ (O : Type) [Ring O] (r : ℕ) (e : Fin r → O),
    Submodule.span ℤ (Set.range e) = ⊤ → ∃ (m : ℕ) (N : Fin m → Fin r → ℤ) (c1 : Fin r → ℤ)
      (cm : Fin r → Fin r → Fin r → ℤ), ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
      (f : Fin r → (A ⟶ A)), (∀ k, IsMonHom (f k)) → ((∃ act : O → (A ⟶ A), IsRAct A act ∧ ∀ k, act (e k) = f k) ↔
        ((∀ j, ∏ k, f k ^ N j k = 1) ∧ ∏ k, f k ^ c1 k = 𝟙 A ∧
          ∀ i j, f i ≫ f j = ∏ k, f k ^ cm i j k)) := by
  intro O _ r e he
  let φ : (Fin r → ℤ) →ₗ[ℤ] O :=
    { toFun := fun c => ∑ k, c k • e k
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun n c => by simp [Finset.smul_sum, mul_smul] }
  have hφ : ∀ c, φ c = ∑ k, c k • e k := fun _ => rfl
  have hsurj : ∀ a, ∃ c, φ c = a := fun a => by
    have : a ∈ Submodule.span ℤ (Set.range e) := he ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp this
    exact ⟨c, hc⟩
  obtain ⟨m, N, hN⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (LinearMap.ker φ))
  choose coef hcoef using hsurj
  refine ⟨m, N, coef 1, fun i j => coef (e i * e j), ?_⟩
  intro S A _ _ f hf
  have hker : (∀ j, prodPow f (N j) = 1) → ∀ c ∈ LinearMap.ker φ, prodPow f c = 1 := by
    intro hNj c hc
    rw [← hN] at hc
    induction hc using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hNj j
    | zero => exact prodPow_zero f
    | add x y _ _ hx hy => rw [prodPow_add, hx, hy, _root_.mul_one]
    | smul n x _ hx => rw [prodPow_zsmul, hx, one_zpow]
  have hwd : (∀ j, prodPow f (N j) = 1) → ∀ c d, φ c = φ d → prodPow f c = prodPow f d := by
    intro hNj c d h
    have hcd : c - d ∈ LinearMap.ker φ := by simp [LinearMap.mem_ker, map_sub, h]
    calc prodPow f c = prodPow f (d + (c - d)) := by rw [add_sub_cancel]
      _ = prodPow f d := by rw [prodPow_add, hker hNj _ hcd, _root_.mul_one]
  have hmul : ∀ c d : Fin r → ℤ, φ c * φ d = ∑ k, ∑ l, (c k * d l) • (e k * e l) := by
    intro c d
    rw [hφ, hφ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_smul]
  constructor
  · rintro ⟨act, hact, hek⟩
    have h0 : act 0 = 1 := by
      have := hact.2.2.2 0 0
      rw [add_zero] at this
      exact mul_eq_left.mp this.symm
    let H : Multiplicative O →* (A ⟶ A) :=
      MonoidHom.mk' (fun a => act a.toAdd) (fun a b => hact.2.2.2 a.toAdd b.toAdd)
    have hact' : ∀ c, act (φ c) = prodPow f c := by
      intro c
      have : act (φ c) = H (Multiplicative.ofAdd (∑ k, c k • e k)) := rfl
      rw [this, ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [ofAdd_zsmul, map_zpow]
      show act (e k) ^ c k = _
      rw [hek]
    refine ⟨fun j => ?_, ?_, fun i j => ?_⟩
    · show prodPow f (N j) = 1
      have hNj : N j ∈ LinearMap.ker φ := hN ▸ Submodule.subset_span ⟨j, rfl⟩
      rw [← hact', LinearMap.mem_ker.mp hNj, h0]
    · show prodPow f (coef 1) = 𝟙 A
      rw [← hact', hcoef, hact.2.1]
    · show f i ≫ f j = prodPow f (coef (e i * e j))
      rw [← hact', hcoef, hact.2.2.1, hek, hek]
  · rintro ⟨hNj, h1, hm⟩
    refine ⟨fun a => prodPow f (coef a), ⟨fun a => isMonHom_prodPow f hf _, h1, fun a b => ?_, fun a b => ?_⟩,
      fun k => ?_⟩
    · rw [prodPow_comp f hf _ hm]
      apply hwd hNj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hcoef, map_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul, hcoef]
      rw [← hmul, hcoef, hcoef]
    · rw [← prodPow_add]
      apply hwd hNj
      rw [map_add (f := _), hcoef, hcoef, hcoef]
    · show prodPow f (coef (e k)) = f k
      rw [hwd hNj (coef (e k)) (Pi.single k 1) (by rw [hcoef, hφ]; simp [Pi.single_apply]),
        prodPow_single]

end GlobalTheory.ActRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotient
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.EtaleLie

variable {S : Scheme.{0}}

theorem fst_spMap_epsScaleR {R' : Type} [CommRing R'] (c : R') :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (epsScaleR c) =
      spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r

theorem existsUnique_dual_lift {R' : Type} [CommRing R'] {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B)
    [IsMonHom ψ] [Etale ψ.left] (x : Sp R' ⟶ S) (h : Sp (DualNumber R') ⟶ B.left)
    (hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ h = (1 : Over.mk x ⟶ B).left) :
    ∃! l : Sp (DualNumber R') ⟶ A.left,
      spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ l = (1 : Over.mk x ⟶ A).left ∧ l ≫ ψ.left = h := by
  let π : CommRingCat.of (DualNumber R') ⟶ CommRingCat.of R' :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber R', a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  refine GlobalTheory.existsUnique_lift_of_etale_of_surjective ψ.left π hπ hnil _ h ?_
  show (1 : Over.mk x ⟶ A).left ≫ ψ.left = spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ h
  rw [hh]
  exact congrArg (·.left) (MonObj.one_comp ψ)

theorem lie_of_etale : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A') (Ga : Type) [Group Ga] (ρ : Ga → (o.A.left ⟶ o.A.left)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover Ga ρ ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ A', IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A'), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b M S s o A' _ _ act' ψ Ga _ ρ _hab hψ hG hact
  haveI := hψ
  haveI : Etale ψ.left := hG.etale
  refine ⟨?_, ?_⟩
  · intro R' _ β x hx v hv
    obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := existsUnique_dual_lift ψ x v.left hv.1
    let u : epsPtR x ⟶ o.A := Over.homMk l (by
      show l ≫ o.A.hom = _
      rw [← Over.w ψ, ← Category.assoc, hl₂]; exact Over.w v)
    have hu : IsTanScal o.act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) u := by
      refine ⟨hl₁, ?_⟩
      have hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ (spMap (epsScaleR (β b.ρ)) ≫ v.left) =
          (1 : Over.mk x ⟶ A').left := by
        rw [← Category.assoc, fst_spMap_epsScaleR, hv.1]
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O D.ω)
      refine (existsUnique_dual_lift ψ x _ hh).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · show _ ≫ l ≫ (o.act.act _).left = _
        rw [← Category.assoc, hl₁]
        have e : ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O D.ω)).left = (1 : Over.mk x ⟶ o.A).left :=
          congrArg Over.Hom.left (MonObj.one_comp _)
        exact e
      · show (l ≫ (o.act.act _).left) ≫ ψ.left = _
        rw [Category.assoc, ← Over.comp_left, hact, Over.comp_left, ← Category.assoc, hl₂, ← hv.2]
        rfl
      · show _ ≫ spMap _ ≫ l = _
        rw [← Category.assoc, fst_spMap_epsScaleR, hl₁]
      · show (spMap _ ≫ l) ≫ ψ.left = _
        rw [Category.assoc, hl₂]
    obtain ⟨w, hw, hvw⟩ := o.lie R' β x hx u hu
    refine ⟨fun i => w i ≫ ψ, fun i c => ⟨?_, ?_⟩, ?_⟩
    · show _ ≫ (w i).left ≫ ψ.left = _
      rw [← Category.assoc, (hw i c).1]
      have e : ((1 : Over.mk x ⟶ o.A) ≫ ψ).left = (1 : Over.mk x ⟶ A').left :=
        congrArg Over.Hom.left (MonObj.one_comp ψ)
      exact e
    · show ((w i ≫ ψ) ≫ act'.act _).left = spMap _ ≫ (w i).left ≫ ψ.left
      rw [Category.assoc, ← hact, ← Category.assoc, Over.comp_left, (hw i c).2, Category.assoc]
    · apply Over.OverMorphism.ext
      rw [← GlobalTheory.LieEtale.ofFn_prod_comp ψ w, ← hvw]
      exact hl₂.symm
  · intro κ _ _ x β hx i
    exact (GlobalTheory.LieEtale.lieMult_iff_of_etale (𝓞 D.F) S o.A A' ψ (o.act.toF D) (act'.toF D) hψ hG.etale
      (fun c => hact _) κ x (β.comp (b.t i)) D.m).mp (o.lieRank κ x β hx i)

end GlobalTheory.UPel.HT.EtaleLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatio
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem eval_coe_polynomial_of_isEval {p : ℕ} {B : Type} [CommRing B] {σ : Type}
    (z : σ → B) (E : MvPowerSeries σ B →ₐ[B] B) (hE : IsEval p z E) (P : MvPolynomial σ B) :
    E (P : MvPowerSeries σ B) = MvPolynomial.eval z P := by
  have h : E.comp (MvPolynomial.coeToMvPowerSeries.algHom B) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, hE.1 i]
  have := congrArg (fun φ => φ P) h
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this

theorem hasVal_map_of_isEval : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ s : MvPowerSeries σ B, HasVal p z (map (algebraMap B Q) s) (algebraMap B Q (E s)) := by
  intro p _ B O Q _ _ _ _ θ _ σ _ _ z _ E hE s m
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun N' hN' => ?_⟩
  set n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N'
  have hdiv : (p : B) ^ m ∣ E (s - (trunc' B n s : MvPowerSeries σ B)) := by
    apply hN
    intro α hα
    have hle : α ≤ n := by
      intro i
      have h1 : α i ≤ α.degree := by
        classical
        rw [Finsupp.degree]
        by_cases hi : i ∈ α.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · simp [Finsupp.notMem_support_iff.1 hi]
      show α i ≤ N'
      omega
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨b, ?_⟩
  rw [map_sub, eval_coe_polynomial_of_isEval z E hE] at hb
  have key : algebraMap B Q (MvPolynomial.eval z (trunc' B n s)) =
      MvPolynomial.eval₂ (algebraMap B Q) (fun i => algebraMap B Q (z i)) (trunc' B n s) := by
    rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
    exact MvPolynomial.eval₂_comp_left _ _ _ _
  rw [trunc'_map, MvPolynomial.eval_map, ← key, ← map_sub, hb]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubAFiniteFree
section
noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def heckeSubA {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (f : D.La →+ D.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • f x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add (f := _), smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

theorem mem_heckeSubA {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (f : D.La →+ D.La) (N : ℕ)
    (x : D.La) : o.eta (N • f x) ∈ heckeSubA o f N := ⟨x, rfl⟩

theorem eta_pow {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (n : ℕ) (z : D.La) :
    (o.eta z) ^ n = o.eta (n • z) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, eta_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, o.eta_add]

theorem pow_eq_one_of_mem {b : Base D R} {N k : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (f : D.La →+ D.La)
    (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ∈ heckeSubA o f N) : h ^ k = 1 := by
  obtain ⟨x, rfl⟩ := hh
  rw [eta_pow, smul_smul, show k * N = N * k from mul_comm _ _, o.eta_ker]

theorem act_mem {b : Base D R} {N k : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (f : D.La →+ D.La)
    (hf : ∀ (a : D.O) (x : D.La), ∃ z, f (a • x) = a • f x + (N * k) • z) (a : D.O)
    (h : 𝟙_ (Over S) ⟶ o.A) (hh : h ∈ heckeSubA o f N) : h ≫ o.act.act a ∈ heckeSubA o f N := by
  obtain ⟨x, rfl⟩ := hh
  obtain ⟨z, hz⟩ := hf a x
  refine ⟨a • x, ?_⟩
  rw [hz, smul_add, o.eta_add, smul_smul, show N * (N * k) = (N * k) * N from mul_comm _ _, ← smul_smul,
    o.eta_ker, _root_.mul_one, ← o.eta_lin, smul_comm]

theorem heckeSubA_finite_free (b : Base D R) (f : D.La →+ D.La) (k N : ℕ) (hk : 0 < k) (hN : 0 < N)
    (hkp : k.Coprime p) (hNp : N.Coprime p) (s : S ⟶ Sp R) (o : Obj b (N * k) s) :
    Finite (heckeSubA o f N) ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A),
      h ∈ heckeSubA o f N → toUnit (Over.mk x) ≫ h = 1 → h = 1 := by
  refine ⟨?_, ?_⟩
  · haveI := D.finLa
    let K : Submodule ℤ D.La := LinearMap.range ((k : ℤ) • LinearMap.id)
    haveI : Finite (D.La ⧸ K) := by
      apply Module.finite_of_fg_torsion
      intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K q
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show (k : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, by simp⟩
    let σ := Function.surjInv (Submodule.Quotient.mk_surjective K)
    refine Finite.of_surjective
      (fun q : D.La ⧸ K => (⟨o.eta (N • f (σ q)), mem_heckeSubA o f N _⟩ : heckeSubA o f N)) ?_
    rintro ⟨h, x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, Subtype.ext ?_⟩
    have e : Submodule.Quotient.mk (σ (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk x : D.La ⧸ K) :=
      Function.surjInv_eq _ _
    rw [Submodule.Quotient.eq] at e
    obtain ⟨z, hz⟩ := e
    have hz' : σ (Submodule.Quotient.mk x) = x + k • z := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hz
      rw [hz]; abel
    show o.eta (N • f (σ (Submodule.Quotient.mk x))) = o.eta (N • f x)
    rw [hz', map_add (f := _), map_nsmul, smul_add, smul_smul, o.eta_add, o.eta_ker, _root_.mul_one]
  · intro κ _ _ x h hh h1
    obtain ⟨x0, rfl⟩ := hh
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
    obtain ⟨I, hI⟩ := o.geom κ x _ hβ
    have h2 : I.ev (N * k) (N • f x0) = 1 := by rw [← hI]; exact h1
    obtain ⟨y, hy⟩ := (I.ker (N * k) (Nat.mul_pos hN hk) (Nat.Coprime.mul_left hNp hkp) _).1 h2
    rw [hy, o.eta_ker]

end GlobalTheory.UPel.HT.HeckeAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubFiniteFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem heckeSub_finite_free : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), Finite (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A), h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N → toUnit (Over.mk x) ≫ h = 1 → h = 1 := by
  intro p _ D R _ b g k N hk hN hkp hNp S s o
  refine ⟨?_, ?_⟩
  · haveI := D.finLa
    let K : Submodule ℤ D.La := LinearMap.range ((k : ℤ) • LinearMap.id)
    haveI : Finite (D.La ⧸ K) := by
      apply Module.finite_of_fg_torsion
      intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K q
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show (k : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, by simp⟩
    let σ := Function.surjInv (Submodule.Quotient.mk_surjective K)
    refine Finite.of_surjective (fun q : D.La ⧸ K => (⟨o.eta (N • g (σ q)), mem_heckeSub o g N _⟩ : heckeSub o g N)) ?_
    rintro ⟨h, x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, Subtype.ext ?_⟩
    have e : Submodule.Quotient.mk (σ (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk x : D.La ⧸ K) :=
      Function.surjInv_eq _ _
    rw [Submodule.Quotient.eq] at e
    obtain ⟨z, hz⟩ := e
    have hz' : σ (Submodule.Quotient.mk x) = x + k • z := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hz
      rw [hz]; abel
    show o.eta (N • g (σ (Submodule.Quotient.mk x))) = o.eta (N • g x)
    rw [hz', map_add (f := _), map_nsmul, smul_add, smul_smul, o.eta_add, o.eta_ker, _root_.mul_one]
  · intro κ _ _ x h hh h1
    obtain ⟨x0, rfl⟩ := hh
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
    obtain ⟨I, hI⟩ := o.geom κ x _ hβ
    have h2 : I.ev (N * k) (N • g x0) = 1 := by rw [← hI]; exact h1
    obtain ⟨y, hy⟩ := (I.ker (N * k) (Nat.mul_pos hN hk) (Nat.Coprime.mul_left hNp hkp) _).1 h2
    rw [hy, o.eta_ker]

end GlobalTheory.UPel.HT.Hecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureTorsorEtaleHeightOneAbhyankarStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_torsor_etale_height_one_abhyankar : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], P₁.height ≤ 1 → algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∈ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  first | (exact @GlobalTheory.KeyOriginBC.closureEtaleAt_of_mem_height_le_one) | (exact GlobalTheory.KeyOriginBC.closureEtaleAt_of_mem_height_le_one) | (intros; apply GlobalTheory.KeyOriginBC.closureEtaleAt_of_mem_height_le_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesLinearCoefficientsMvPowerSeriesFormal
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.FormalCalc

theorem lin_formalLog (Q : Type) [CommRing Q] [Algebra ℚ Q] (d : ℕ) (g : MvPowerSeries (Fin d) Q) :
    constantCoeff g = 1 → ∀ i, lin (formalLog g) i = lin g i := by
  intro hg i
  have h := congrArg (coeff (0 : Fin d →₀ ℕ)) (mul_pderiv_formalLog hg i)
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, hg, one_mul, ← coeff_zero_eq_constantCoeff_apply,
    coeff_pderiv, coeff_pderiv] at h
  simpa [lin] using h

end GlobalTheory.FormalCalc
end

