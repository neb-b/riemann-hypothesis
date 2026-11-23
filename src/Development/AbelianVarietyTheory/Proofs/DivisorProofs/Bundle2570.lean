module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedPullbackConjugateTranslateEqTranslateL
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MemOfIsIntegralElem
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThListConj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.GalConj
open GlobalTheory.UMin.GalTh

theorem coe_mul {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (τ₁ τ₂ : K ≃ₐ[Ω] K) :
    ((τ₁ * τ₂ : K ≃ₐ[Ω] K) : K →+* K) = (τ₁ : K →+* K).comp (τ₂ : K →+* K) := RingHom.ext fun _ => rfl

theorem coe_one {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] :
    ((1 : K ≃ₐ[Ω] K) : K →+* K) = RingHom.id K := RingHom.ext fun _ => rfl

theorem comp_alg {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (τ : K ≃ₐ[Ω] K) :
    (τ : K →+* K).comp (algebraMap Ω K) = algebraMap Ω K := RingHom.ext fun r => τ.commutes r

theorem thList_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω K : Type) [Field Ω] [Field K] [IsAlgClosed K] [Algebra Ω K] (x : Sp Ω ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk (spMap (algebraMap Ω K) ≫ x) ⟶ G)) (c : Fin N → K), Odd m → (m : K) ≠ 0 → PolFib G L g (spMap (algebraMap Ω K) ≫ x) → ThList G L ρ m (spMap (algebraMap Ω K) ≫ x) (SecAt.pull G L θ (algebraMap Ω K)) pt c → ∃ φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin N), ∀ (τ : K ≃ₐ[Ω] K) (a : Fin N), spMap (τ : K →+* K) ≫ (pt a).left = (pt (φ τ a)).left ∧ τ (c a) = c (φ τ a) := by
  intro S G _ _ L ρ hL hρ g m N Ω K _ _ _ _ x θ pt c hm hmK hpol hK
  classical
  have hfix : ∀ τ : K ≃ₐ[Ω] K, spMap (τ : K →+* K) ≫ (Over.mk (spMap (algebraMap Ω K) ≫ x)).hom = (Over.mk (spMap (algebraMap Ω K) ≫ x)).hom := fun τ => by
    show spMap (τ : K →+* K) ≫ spMap (algebraMap Ω K) ≫ x = spMap (algebraMap Ω K) ≫ x
    rw [← Category.assoc, ← GalTh.sp_comp, comp_alg]
  let u : (K ≃ₐ[Ω] K) → (Over.mk (spMap (algebraMap Ω K) ≫ x) ⟶ Over.mk (spMap (algebraMap Ω K) ≫ x)) := fun τ => Over.homMk (spMap (τ : K →+* K)) (hfix τ)
  have hul : ∀ τ, (u τ).left = spMap (τ : K →+* K) := fun τ => Over.homMk_left _ _
  have hu1 : u 1 = 𝟙 _ := Over.OverMorphism.ext (by rw [hul, coe_one, GalTh.sp_id]; rfl)
  have humul : ∀ τ₁ τ₂, u (τ₁ * τ₂) = u τ₁ ≫ u τ₂ := fun τ₁ τ₂ =>
    Over.OverMorphism.ext (by rw [Over.comp_left, hul, hul, hul, coe_mul, GalTh.sp_comp])
  have htor : ∀ τ a, (u τ ≫ pt a) ^ (m ^ 2) = 1 := fun τ a => by
    rw [← MonObj.comp_pow, (hK.2.1 a).1, MonObj.comp_one]
  choose f hf using fun τ a => thList_exh hK (u τ ≫ pt a) (htor τ a)
  have hf1 : ∀ a, f 1 a = a := fun a => hK.1 (by rw [← hf, hu1, Category.id_comp])
  have hfmul : ∀ τ₁ τ₂ a, f (τ₁ * τ₂) a = f τ₁ (f τ₂ a) := fun τ₁ τ₂ a => hK.1 (by
    rw [← hf, ← hf, ← hf, humul, Category.assoc])
  let P : (K ≃ₐ[Ω] K) → Equiv.Perm (Fin N) := fun τ =>
    { toFun := f τ, invFun := f τ⁻¹
      left_inv := fun a => by rw [← hfmul, inv_mul_cancel, hf1]
      right_inv := fun a => by rw [← hfmul, mul_inv_cancel, hf1] }
  let φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin N) :=
    { toFun := P
      map_one' := Equiv.ext fun a => hf1 a
      map_mul' := fun τ₁ τ₂ => Equiv.ext fun a => hfmul τ₁ τ₂ a }
  have hφ : ∀ τ a, φ τ a = f τ a := fun _ _ => rfl
  have hleft : ∀ (τ : K ≃ₐ[Ω] K) a, spMap (τ : K →+* K) ≫ (pt a).left = (pt (f τ a)).left := fun τ a => by
    rw [← hf, Over.comp_left, hul]
  refine ⟨φ, fun τ a => ⟨by rw [hφ]; exact hleft τ a, ?_⟩⟩
  rw [hφ]
  obtain ⟨pt', hpt', h'⟩ := GlobalTheory.UMin.ThPull.thList_pull S G L ρ hL hρ m N K K (τ : K →+* K) (spMap (algebraMap Ω K) ≫ x)
    (SecAt.pull G L θ (algebraMap Ω K)) pt c hK
  obtain ⟨pt₃, hpt₃, h₃⟩ := thList_comp m (algebraMap Ω K) (τ : K →+* K) (algebraMap Ω K) (comp_alg τ) x θ pt' _ h'
  have e3 : pt₃ a = pt (f τ a) := Over.OverMorphism.ext (by rw [hpt₃, hpt', hleft])
  have q := h₃.2.1 a
  rw [e3] at q
  have hθ : SecM.ofSec G (SecAt.pull G L θ (algebraMap Ω K)) =
      @id Γ((Over.mk (spMap (algebraMap Ω K) ≫ x)).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) • SecM.ofSec G (SecAt.pull G L θ (algebraMap Ω K)) := by
    rw [id, show GlobalTheory.ZH.fn (1 : K) = 1 from map_one _, one_smul]
  have r := (GlobalTheory.UMin.thG_smul_iff S G L ρ hL hρ g m K (spMap (algebraMap Ω K) ≫ x) _ _ (pt (f τ a)) 1 (c (f τ a)) (τ (c a)) hm hmK hpol hθ
    (hK.2.1 (f τ a))).1 q
  rw [r, _root_.one_mul]

end GlobalTheory.UMin.GalConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListsUniqueUpToPermScalar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.ThUniq

theorem comp_pow' {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem exists_perm_pts {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N : ℕ} {pt q : Fin N → (Over.mk x ⟶ G)}
    {c d : Fin N → K} (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' q d) :
    ∃ σ : Equiv.Perm (Fin N), ∀ b, q b = pt (σ b) := by
  have key : ∀ b, ∃ a, q b = pt a := by
    intro b
    let i := algebraMap K (AlgebraicClosure K)
    let u : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
    have hp : (u ≫ q b) ^ (m ^ 2) = 1 := by
      rw [← comp_pow', (h'.2.1 b).1, MonObj.comp_one]
    obtain ⟨a, ha⟩ := h.2.2 (AlgebraicClosure K) i (u ≫ q b) hp
    refine ⟨a, Over.OverMorphism.ext ?_⟩
    have : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
    exact (cancel_epi (spMap i)).1 (by rw [← ha, Over.comp_left]; rfl)
  choose f hf using key
  have hinj : Function.Injective f := fun b b' e => h'.1 ((hf b).trans ((congrArg pt e).trans (hf b').symm))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

end GlobalTheory.UMin.ThUniq

namespace GlobalTheory.UMin.ThUniq

theorem theta_lists_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m m' N N' : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S), Odd m → (m : K) ≠ 0 → Odd m' → (m' : K) ≠ 0 → PolFib G L g x → (∀ (θ : SecAt G L x) (pt pt' : Fin N → (Over.mk x ⟶ G)) (c d : Fin N → K), ThList G L ρ m x θ pt c → ThList G L ρ m x θ pt' d → ∃ σ : Equiv.Perm (Fin N), ∀ b, d b = c (σ b)) ∧ ∀ (c d : Fin N → K) (c' d' : Fin N' → K), HasTh₂ G L ρ m m' x c c' → HasTh₂ G L ρ m m' x d d' → ∃ (a : K) (σ : Equiv.Perm (Fin N)) (σ' : Equiv.Perm (Fin N')), a ≠ 0 ∧ (∀ b, d b = a * c (σ b)) ∧ ∀ b, d' b = a * c' (σ' b) := by
  intro S G _ _ L ρ hL hρ g m m' N N' K _ x hm hmK hm' hmK' hpol
  have tv : ∀ (k : ℕ), Odd k → (k : K) ≠ 0 → ∀ (θ θ' : SecAt G L x) (p : Over.mk x ⟶ G) (a c c' : K),
      SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ →
      ThG G L ρ k θ p (GlobalTheory.ZH.fn c) → ThG G L ρ k θ' p (GlobalTheory.ZH.fn c') → c' = a * c :=
    fun k hk hkK θ θ' p a c c' hs hc hc' =>
      (_root_.GlobalTheory.UMin.thG_smul_iff S G L ρ hL hρ g k K x θ θ' p a c c' hk hkK hpol hs hc).1 hc'
  have gen : ∀ θ θ' : SecAt G L x, IsGenSec G L _ θ →
      ∃ a : K, SecM.ofSec G θ' = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn a) • SecM.ofSec G θ := by
    intro θ θ' h
    obtain ⟨r, hr⟩ := h θ'
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r, ?_⟩
    have e : @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r)) = r := by
      show ((Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom r = r
      rw [Iso.hom_inv_id]; rfl
    rw [e]
    exact Subtype.ext (funext hr)
  refine ⟨fun θ pt pt' c d h h' => ?_, fun c d c' d' H H' => ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_perm_pts h h'
    refine ⟨σ, fun b => ?_⟩
    have e1 : SecM.ofSec G θ = @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) • SecM.ofSec G θ := by
      rw [show @id Γ((Over.mk x).left, ⊤) (GlobalTheory.ZH.fn (1 : K)) = 1 from map_one _, one_smul]
    rw [tv m hm hmK θ θ (pt (σ b)) 1 (c (σ b)) (d b) e1 (h.2.1 (σ b)) (by rw [← hσ b]; exact h'.2.1 b), _root_.one_mul]
  · obtain ⟨θ, pt, pt', hg, h1, h1'⟩ := H
    obtain ⟨θ₂, q, q', hg₂, h2, h2'⟩ := H'
    obtain ⟨σ, hσ⟩ := exists_perm_pts h1 h2
    obtain ⟨σ', hσ'⟩ := exists_perm_pts h1' h2'
    obtain ⟨a₀, ha₀⟩ := gen θ θ₂ hg
    obtain ⟨a₁, ha₁⟩ := gen θ₂ θ hg₂
    have E : ∀ b, d b = a₀ * c (σ b) := fun b =>
      tv m hm hmK θ θ₂ _ a₀ _ _ ha₀ (h1.2.1 (σ b)) (by rw [← hσ b]; exact h2.2.1 b)
    have E' : ∀ b, d' b = a₀ * c' (σ' b) := fun b =>
      tv m' hm' hmK' θ θ₂ _ a₀ _ _ ha₀ (h1'.2.1 (σ' b)) (by rw [← hσ' b]; exact h2'.2.1 b)
    by_cases h0 : a₀ = 0
    · have F : ∀ b, c (σ b) = a₁ * d b := fun b =>
        tv m hm hmK θ₂ θ _ a₁ _ _ ha₁ (by rw [← hσ b]; exact h2.2.1 b) (h1.2.1 (σ b))
      have F' : ∀ b, c' (σ' b) = a₁ * d' b := fun b =>
        tv m' hm' hmK' θ₂ θ _ a₁ _ _ ha₁ (by rw [← hσ' b]; exact h2'.2.1 b) (h1'.2.1 (σ' b))
      refine ⟨1, σ, σ', one_ne_zero, fun b => ?_, fun b => ?_⟩
      · have e := E b
        rw [h0, MulZeroClass.zero_mul] at e
        rw [F b, e, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
      · have e := E' b
        rw [h0, MulZeroClass.zero_mul] at e
        rw [F' b, e, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
    · exact ⟨a₀, σ, σ', h0, E, E'⟩

end GlobalTheory.UMin.ThUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilySectionEquivarianceSmulOfNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.ScaleEqv

theorem eqv_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) lab E, Eqv D A F N lab E → ∀ c : Fˣ, ∃ E', Eqv D A F N lab E' ∧ ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  intro R _ _ D A F _ _ N lab E h c
  let gg : F →+* Γ((TFK (R := R) F ⊗ A.A).left, ⊤) :=
    (fst (TFK (R := R) F) A.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hgg : ∀ u : F, gg u = (fst (TFK (R := R) F) A.A).left.appTop.hom (fnF F u) := fun _ => rfl
  have inv1 : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens) (u : Fˣ), resTop W (gg u.val) * resTop W (gg (u⁻¹).val) = 1 := by
    intro W u
    simp only [resTop]
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  let S : F → SecK A.L (snd (TFK (R := R) F) A.A).left N → SecK A.L (snd (TFK (R := R) F) A.A).left N :=
    fun u t => DVR.SecOps.secScale (gg u) t
  have Sf : ∀ u t j, (S u t).f j = resTop _ (gg u) * t.f j := fun _ _ _ => rfl
  have SS : ∀ (u : Fˣ) t, S u.val (S (u⁻¹).val t) = t := by
    intro u t
    apply DVR.SecOps.sec_ext
    intro j
    rw [Sf, Sf, ← _root_.mul_assoc, inv1, _root_.one_mul]
  have SS' : ∀ (u : Fˣ) t, S (u⁻¹).val (S u.val t) = t := by
    intro u t
    have := SS u⁻¹ t
    rwa [inv_inv] at this
  refine ⟨fun s => S c.val (E s), ⟨?_, ?_, ?_, h.onto, h.frame, h.lift, ?_⟩, fun s j => rfl⟩
  · constructor
    · intro s t hst
      apply h.bij.1
      have := congrArg (S (c⁻¹).val) hst
      simpa only [SS'] using this
    · intro t
      obtain ⟨s, hs⟩ := h.bij.2 (S (c⁻¹).val t)
      exact ⟨s, by simp only [hs, SS]⟩
  · intro s s' s'' hs j
    simp only [Sf]
    rw [h.add s s' s'' hs j, mul_add]
  · intro u s s' hs j
    simp only [Sf]
    rw [h.smul u s s' hs j, mul_left_comm]
  · intro p w θ s s' hw hθ hph j
    have key := h.act p w θ s s' hw hθ hph j
    have e : (translT A.A θ.pt).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left := by
      rw [← Over.comp_left, translT, lift_fst]
    have hψ : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens),
        ((translT A.A θ.pt).left.app W).hom (resTop W (gg c.val)) =
          resTop ((translT A.A θ.pt).left ⁻¹ᵁ W) (gg c.val) := by
      intro W
      simp only [resTop]
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
      congr 1
      rw [hgg]
      have hT : ((translT A.A θ.pt).left.appTop).hom (((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val)) =
          ((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val) := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
      exact hT
    erw [Sf, Sf]
    erw [map_mul, map_mul, map_mul, hψ, key, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, mul_left_comm]

end GlobalTheory.Mum.ScaleEqv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupOfPointEqAlongModelHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.HHFibre

open GlobalTheory.ZH GlobalTheory.ZH.RatModel

theorem isHom_of_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω} {q : Y.Z ⟶ M.Z}
    (hq : Y.pt ≫ q = M.pt) : M.IsHom Y (AlgHom.id o Ω) q := by
  show Y.pt ≫ q = spMap (AlgHom.id o Ω).toRingHom ≫ M.pt
  rw [hq]
  have : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _
    rw [← Spec.map_id]; rfl
  rw [this, Category.id_comp]

theorem exists_pt (X : Scheme.{0}) (w : X) : ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X),
    y (IsLocalRing.closedPoint K) = w :=
  ⟨X.residueField w, inferInstance, X.fromSpecResidueField w, Scheme.fromSpecResidueField_apply _ _⟩

theorem isUnit_of_isUnit_comap {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω}
    {q : Y.Z ⟶ M.Z} (hq : M.IsHom Y (AlgHom.id o Ω) q) (w : Y.Z) {a : Ω} (ha : a ∈ M.O (q w))
    (ha' : a ∈ Y.O w) (hu : IsUnit (⟨a, ha'⟩ : Y.O w)) : IsUnit (⟨a, ha⟩ : M.O (q w)) := by
  obtain ⟨K, _, y, hy0⟩ := exists_pt Y.Z w
  have hy : Set.range y = {w} := hy0 ▸ range_eq_singleton y (IsLocalRing.closedPoint K)
  have hyq : Set.range (y ≫ q) = {q w} := by
    have := range_eq_singleton (y ≫ q) (IsLocalRing.closedPoint K)
    refine this.trans ?_
    rw [← hy0]
    rfl
  rw [← val_ne_zero_iff hyq]
  rw [← val_ne_zero_iff hy] at hu
  have ha2 : a ∈ M.O (q (y (IsLocalRing.closedPoint K))) := by rw [hy0]; exact ha
  have e := hq.val_comp y (IsLocalRing.closedPoint K) ha2
  simp only [AlgHom.id_apply] at e
  show M.val (y ≫ q) a ≠ 0
  rw [e]
  exact hu

theorem HH_eq_of_hom : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M Y : RatModel o Ω)
    (q : Y.Z ⟶ M.Z), Y.pt ≫ q = M.pt → M.HasDiv S.th → ∀ w : Y.Z, S.HH Y w = S.HH M (q w) := by
  intro o Ω _ _ _ S M Y q hq hdiv w
  have hh := isHom_of_pt hq
  unfold ThetaSys.HH
  congr 1
  ext x
  simp only [ThetaSys.supI, Set.mem_setOf_eq]
  constructor
  · intro hx
    obtain ⟨x₀, h₀⟩ := hdiv (q w)
    have h₀' : Y.Div S.th x₀ w := by simpa using hh.div h₀
    rw [h₀.div_iff_isUnit]
    exact isUnit_of_isUnit_comap hh w _ _ ((h₀'.div_iff_isUnit x).1 hx)
  · intro hx
    simpa using hh.div hx

end GlobalTheory.Poinc.HHFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupPowValueEqOfConjugateTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaPowConj

theorem prod_telescope {U : Type} [CommGroup U] (F G : ℕ → U) (n : ℕ) :
    ∏ i ∈ Finset.range n, (F i * G i * (F (i + 1))⁻¹) = F 0 * (∏ i ∈ Finset.range n, G i) * (F n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
    group

theorem val_powGen_transport : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (N : ℕ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : ∀ i : ℕ, f ≫ (translT A (θ.pt ^ i)).left = (translT A' (θ'.pt ^ i)).left ≫ f) (hN : θ'.pt ^ N = 1) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (powGen A L k θ N) (q ≫ f) z J = val (powGen A' L' k θ' N) q z J' := by
  intro S S' A A' _ _ L L' T T' f k N θ θ' Ψ hT hN H Z q z J J' hJ hJ'
  rw [GlobalTheory.ConjPull.val_thetaPow θ N (q ≫ f) z hJ, GlobalTheory.ConjPull.val_thetaPow θ' N q z hJ']
  have step : ∀ i ∈ Finset.range N,
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        ((q ≫ f) ≫ (translT A (θ.pt ^ i)).left) z J =
      Ψ (q ≫ (translT A' (θ'.pt ^ i)).left) z J J' ^ k *
        val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ
          (q ≫ (translT A' (θ'.pt ^ i)).left) z J' *
        (Ψ (q ≫ (translT A' (θ'.pt ^ (i + 1))).left) z J J' ^ k)⁻¹ := by
    intro i _
    have e1 : (q ≫ f) ≫ (translT A (θ.pt ^ i)).left = (q ≫ (translT A' (θ'.pt ^ i)).left) ≫ f := by
      rw [Category.assoc, hT i, Category.assoc]
    have e2 : (q ≫ (translT A' (θ'.pt ^ i)).left) ≫ (translT A' θ'.pt).left =
        q ≫ (translT A' (θ'.pt ^ (i + 1))).left := by
      rw [Category.assoc, ← Over.comp_left, GlobalTheory.PullMove.translT_mul, pow_succ']
    rw [e1, H Z _ z J J' hJ hJ', e2]
  rw [Finset.prod_congr rfl step,
    prod_telescope (fun i => Ψ (q ≫ (translT A' (θ'.pt ^ i)).left) z J J' ^ k)
      (fun i => val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ
          (q ≫ (translT A' (θ'.pt ^ i)).left) z J')]
  simp only [hN, pow_zero]
  rw [mul_comm, ← _root_.mul_assoc, inv_mul_cancel, _root_.one_mul]

end GlobalTheory.ThetaPowConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetryValueEqOfConjugate
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaSymTransport

theorem val_symGen_eq : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (ν : LB.Gen (negLB A L k T)) (ν' : LB.Gen (negLB A' L' k T')) (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt⁻¹).left = (translT A' θ'.pt⁻¹).left ≫ f) (hneg : f ≫ (negT A T).left = (negT A' T').left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Hν : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (snd T' A' ≫ (GrpObj.inv : A' ⟶ A')).left]) (ε := ![k, -k]) ν' q z J' * (Ψ (q ≫ (negT A' T').left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (symGen A L k θ ν) (q ≫ f) z J = val (symGen A' L' k θ' ν') q z J' := by
  intro S S' A A' _ _ _ L L' T T' f k θ θ' ν ν' Ψ hT hneg H Hν Z q z J J' hJ hJ'
  have c₁ : (translT A' θ'.pt⁻¹).left ≫ (translT A' θ'.pt).left = 𝟙 _ := by
    rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, mul_inv_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]
  have c₂ : (negT A' T').left ≫ (translT A' θ'.pt).left = (translT A' θ'.pt⁻¹).left ≫ (negT A' T').left := by
    rw [← Over.comp_left, ← Over.comp_left, GlobalTheory.PullMove.negT_translT]
  have e₁ := H Z (q ≫ (translT A' θ'.pt⁻¹).left) z J J' hJ hJ'
  have e₂ := H Z (q ≫ (negT A' T').left) z J J' hJ hJ'
  have e₃ := Hν Z q z J J' hJ hJ'
  have e₄ := Hν Z (q ≫ (translT A' θ'.pt⁻¹).left) z J J' hJ hJ'
  simp only [Category.assoc, c₁, c₂, Category.comp_id, ← hT, ← hneg] at e₁ e₂ e₄
  rw [GlobalTheory.ConjPull.val_thetaSym _ _ _ _ hJ, GlobalTheory.ConjPull.val_thetaSym _ _ _ _ hJ']
  simp only [Category.assoc]
  rw [e₁, e₂, e₃, e₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

end GlobalTheory.ThetaSymTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesValuesGaloisScalar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.values_galois_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ m : ℕ, Odd m → IsUnit (m : R) → ∀ v : QkPt D.toPre (Kb R) (m ^ 2) → Kb R, (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) (m ^ 2) → QkPt D.toPre C (m ^ 2)) (q : QkPt D.toPre (Kb R) (m ^ 2) → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i)) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) (m ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p' := by
  intro R _ _ _ hR D A lab hT m hm hmu v H σ
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em₀, hW, hφ, hloc, -, -, -, -⟩ := hT
  obtain ⟨C, _, _, _, _, _, _, hC⟩ := GlobalTheory.Ex.StepInh.exists_cExt W hW
  have hg : Function.Injective ((algebraMap (FractionRing W) C).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) C).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) C := (IsFractionRing.lift hg).toAlgebra
  have hA : ∀ r : R, algebraMap (FractionRing R) C (algebraMap R _ r) =
      algebraMap (FractionRing W) C (algebraMap W _ (φ r)) := fun r => IsFractionRing.lift_algebraMap hg r
  haveI := hloc
  have hCR : GlobalTheory.Ex.CExt R (maximalIdeal R) C :=
    ⟨fun r => by rw [hA]; exact hC.1 _, fun r hr => by rw [hA]; exact hC.2 _ (map_nonunit φ r hr)⟩
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, nu, -⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.firstFiveLaws.1 R D.toPre D.psi_even D.tau_bimult C ⊤
    (fun _ => trivial)
  have hB := D.tau_bimult
  let em : Kb R →ₐ[FractionRing R] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hq := ((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult C N nu).2.2.2.2 (m ^ 2)).1
  choose e₁ he₁ using fun i => GlobalTheory.LabTrans.exists_ext hB em i
  choose e₂ he₂ using fun i => GlobalTheory.LabTrans.exists_ext hB σ i
  choose qq hqq using fun x : QkPt D.toPre C (m ^ 2) => (hq x).exists
  obtain ⟨s, hs⟩ := H C hCR em N nu e₁ (fun i => qq (e₁ i)) he₁ (fun i => hqq _)
  obtain ⟨s', hs'⟩ := H C hCR (em.comp σ) N nu (fun i => e₁ (e₂ i)) (fun i => qq (e₁ (e₂ i)))
    (fun i => GlobalTheory.LabTrans.qkExt_trans (he₂ i) (he₁ (e₂ i))) (fun i => hqq _)
  have key : ∀ p p', QkExt σ.toRingHom p p' → em (σ (v p)) = ((s' * s⁻¹ : Cˣ) : C) * em (v p') := by
    intro p p' h
    obtain rfl : e₂ p = p' := GlobalTheory.LabTrans.ext_unique hB σ (he₂ p) h
    have h1 := hs' p
    have h2 := hs (e₂ p)
    rw [AlgHom.comp_apply] at h1
    rw [h1, h2, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left]
  have emi : Function.Injective em := em.toRingHom.injective
  by_cases hex : ∃ p p', QkExt σ.toRingHom p p' ∧ v p' ≠ 0
  · obtain ⟨p₀, p₀', h₀, hv₀⟩ := hex
    have hσ0 : σ (v p₀) ≠ 0 := by
      intro h0
      have k0 := key p₀ p₀' h₀
      rw [h0, map_zero] at k0
      exact hv₀ ((map_eq_zero em).1 ((mul_eq_zero.1 k0.symm).resolve_left (Units.ne_zero _)))
    refine ⟨Units.mk0 (σ (v p₀) / v p₀') (div_ne_zero hσ0 hv₀), fun p p' h => emi ?_⟩
    have hne : em (v p₀') ≠ 0 := (map_ne_zero em).2 hv₀
    rw [Units.val_mk0, map_mul, map_div₀, key p p' h, key p₀ p₀' h₀]
    field_simp
  · push_neg at hex
    refine ⟨1, fun p p' h => ?_⟩
    have k := key p p' h
    rw [hex p p' h, map_zero, mul_zero] at k
    rw [hex p p' h, mul_zero]
    exact (map_eq_zero em).1 k
end
end

