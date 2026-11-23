module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftSystemOfSummandReduction
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

def Sys.cocyclesInIdealExtensions {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} (S : Sys I π s₀) : Submodule R (Z1 S.F) where
  carrier := {z | S.IsIdealValuedLiftSystemCocycle z}
  add_mem' {a b} ha hb U V f := by
    change a.1 U V f + b.1 U V f ∈ _
    exact Ideal.add_mem _ (ha U V f) (hb U V f)
  zero_mem' U V f := Ideal.zero_mem _
  smul_mem' r z hz U V f := by
    change r • z.1 U V f ∈ _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hz U V f)

theorem exists_sys_of_summand : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S' : Sys I π s₀, S'.Full hI → (∃ N, IsCompl (S'.K hI) N) → ∀ K : Submodule R (Cr hI π s₀), (∃ N, IsCompl K N) → K ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) → ∃ S : Sys I π s₀, S.K hI = K := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hR S' hF hN K hN' hsup
  obtain ⟨N, hN⟩ := hN

  have lin := _root_.GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero R I hI (Cr hI π s₀) (S'.K hI) K N hN hsup
  obtain ⟨hKinf, u, hu, hu0, hall⟩ := lin.2 hN'
  have hKN : IsCompl K N := lin.1 hKinf
  have ksup := _root_.GlobalTheory.LiftSys.Sys.mem_K_sup_iff R R₀ I hI π hπ hk X₀ s₀

  have fadd : ∀ (c1 c2 : Cr hI π s₀) (w1 w2 : GlobForm s₀), FormOf hI hk c1 w1 → FormOf hI hk c2 w2 → FormOf hI hk (c1 + c2) (w1 + w2) := by
    rintro c1 c2 w1 w2 ⟨f1, h1, e1⟩ ⟨f2, h2, e2⟩
    exact ⟨f1 + f2, by rw [map_add (f := _), map_add (f := _), h1, h2], by rw [map_add (f := _), Submodule.coe_add, e1, e2]⟩
  have fsmul : ∀ (r : R) (c : Cr hI π s₀) (w : GlobForm s₀), FormOf hI hk c w → FormOf hI hk (r • c) (π r • w) := by
    rintro r c w ⟨f, h, e⟩
    exact ⟨π r • f, by rw [map_smul, h, map_smulₛₗ], by rw [map_smul, Submodule.coe_smul, e]⟩
  have fzero : FormOf hI hk (0 : Cr hI π s₀) 0 := ⟨0, by rw [map_zero, map_zero], by rw [map_zero]; rfl⟩
  have hwd : ∀ (c1 c2 : S'.K hI) (w : GlobForm s₀), FormOf hI hk c1.1 w → FormOf hI hk c2.1 w → u c1 = u c2 := by
    rintro c1 c2 w ⟨f1, h1, e1⟩ ⟨f2, h2, e2⟩
    have hz : cmpForm s₀ (f1 - f2) = 0 := Subtype.ext (by rw [map_sub, Submodule.coe_sub, e1, e2, sub_self]; rfl)
    have hcl := (hG.inj _).2 hz
    rw [map_sub, h1, h2, ← map_sub] at hcl
    have hm := (hR.2 _).1 hcl
    have := hu0 (c1 - c2) (by rw [Submodule.coe_sub]; exact hm)
    rwa [map_sub, sub_eq_zero] at this
  have hex : ∀ c ∈ S'.K hI, ∃ w : GlobForm s₀, FormOf hI hk c w := by
    intro c hc
    have h1 := (ksup S' hR hF c).1 (Submodule.mem_sup_left hc)
    rw [hodgeFiltration_eq_range] at h1
    obtain ⟨f, hf⟩ := h1
    exact ⟨(cmpForm s₀ f).1, f, hf, rfl⟩
  have hexF : ∀ w : GlobForm s₀, ∃ c : S'.K hI, FormOf hI hk c.1 w := by
    intro w
    obtain ⟨f, hf⟩ := hG.surj w
    obtain ⟨c0, hc0⟩ := hR.1 (Form.cl s₀ f)
    have hm : c0 ∈ S'.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) :=
      (ksup S' hR hF c0).2 (by rw [hc0, hodgeFiltration_eq_range]; exact ⟨f, rfl⟩)
    obtain ⟨k, hk', i, hi, rfl⟩ := Submodule.mem_sup.1 hm
    refine ⟨⟨k, hk'⟩, f, ?_, hf⟩
    rw [← hc0, map_add (f := _), (hR.2 i).2 hi, add_zero]
  choose cw hcw using hexF

  let v : GlobForm s₀ →+ CatCoh.H1 S'.F :=
    { toFun := fun w ↦ -S'.r hI (u (cw w))
      map_zero' := by
        rw [hwd (cw 0) 0 0 (hcw 0) fzero, map_zero, map_zero, neg_zero]
      map_add' := fun a b ↦ by
        rw [hwd (cw (a + b)) (cw a + cw b) (a + b) (hcw _) (fadd _ _ _ _ (hcw a) (hcw b)), map_add (f := _), map_add (f := _),
          neg_add] }
  have hvdef : ∀ w, v w = -S'.r hI (u (cw w)) := fun _ ↦ rfl
  have hv : ∀ (r : R) w, v (π r • w) = r • v w := by
    intro r w
    rw [hvdef, hvdef, hwd (cw (π r • w)) (r • cw w) _ (hcw _) (fsmul r _ _ (hcw w)), map_smul, map_smul, smul_neg]
  have hW : ∀ r, π r = 0 → ∀ m ∈ S'.cocyclesInIdealExtensions, r • m = 0 := by
    intro r hr m hm
    have hrI : r ∈ I := by rw [← hk]; exact hr
    apply Subtype.ext
    funext U V a
    change r • m.1 U V a = 0
    rw [Algebra.smul_def]
    have := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (S'.F.obj V)) hrI) (hm U V a)
    rw [← sq, map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  have trans' := _root_.GlobalTheory.LiftSys.locIso_transport R R₀ I hI π hπ hk X₀ s₀
  have hq : ∀ w, ∃ m ∈ S'.cocyclesInIdealExtensions, CatCoh.H1.mk S'.F m = v w := by
    intro w
    obtain ⟨z, z', hz, hmk, -, -⟩ := (trans' S' S' (Sys.LocIso.refl S')).2.2 (-(u (cw w))) (neg_mem (hu (cw w)).1)
    exact ⟨z, hz, by rw [hmk, map_neg]; rfl⟩
  obtain ⟨u', hu's, hu'W, hu'q⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hG.proj (Z1 S'.F)
    (CatCoh.H1 S'.F) S'.cocyclesInIdealExtensions hW (CatCoh.H1.mk S'.F) v hv hq
  obtain ⟨S'', Φ, θ, hdef, hθ⟩ := _root_.GlobalTheory.LiftSys.exists_twist R R₀ I hI π hπ hk X₀ s₀ hG.par S' u' hu'W hu's

  have hle : K ≤ S''.K hI := by
    intro k hk'
    obtain ⟨c, rfl⟩ := hall k hk'
    obtain ⟨w, hw⟩ := hex c.1 c.2
    obtain ⟨zw, -, hzw⟩ := (trans' S' S'' Φ).1 (u' w) (hu'W w)
    have hmain := _root_.GlobalTheory.LiftSys.r_eq_neg_defect R R₀ I hI π hπ hk X₀ s₀ hG.const S' S'' Φ θ hdef c.1 c.2 w hw zw
      (fun U V a ↦ (hzw U V a).trans (hθ w U V a).symm)
    obtain ⟨z, z2, hzI, hz1, hz2, hzz⟩ := (trans' S' S'' Φ).2.2 (u c) (hu c).1
    have heq : u c = u (cw w) := hwd c (cw w) w hw (hcw w)
    have hsum : CatCoh.H1.mk S'.F (z + u' w) = 0 := by
      rw [map_add (f := _), hz1, hu'q w, hvdef, heq, add_neg_cancel]
    obtain ⟨g, hgI, hg⟩ := _root_.GlobalTheory.LiftSys.cobound_I R R₀ I hI π hπ hk X₀ s₀ hG.const S' (z + u' w)
      (S'.cocyclesInIdealExtensions.add_mem hzI (hu'W w)) hsum
    have h2 : CatCoh.H1.mk S''.F (z2 + zw) = 0 := by
      refine CatCoh.H1.mk_eq_zero.2 ⟨fun W ↦ Φ.φ W (g W), ?_⟩
      funext U V a
      rw [(trans' S' S'' Φ).2.1 g hgI U V a, hg]
      change Φ.φ V (z.1 U V a + (u' w).1 U V a) = z2.1 U V a + zw.1 U V a
      rw [map_add (f := _), hzz, hzw]
    rw [map_add (f := _)] at h2
    have h3 := eq_neg_of_add_eq_zero_left h2
    rw [Sys.K, LinearMap.mem_ker, map_sub, hmain, ← hz2, h3, sub_neg_eq_add, neg_add_cancel]

  have kinf := _root_.GlobalTheory.LiftSys.K_inf_eq_and_full R R₀ I hI π hπ hk X₀ s₀ hG.const
  have hF'' : S''.Full hI := (kinf S' S'').2 hF
  have hsup'' : S''.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊔ I • ⊤ := by
    ext c
    rw [ksup S'' hR hF'' c, ksup S' hR hF c]
  have hS''N : IsCompl (S''.K hI) N :=
    (_root_.GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero R I hI (Cr hI π s₀) (S'.K hI) (S''.K hI) N hN hsup'').1 ((kinf S'' S').1)
  refine ⟨S'', le_antisymm ?_ hle⟩
  calc S''.K hI = (K ⊔ N) ⊓ S''.K hI := by rw [hKN.sup_eq_top, top_inf_eq]
    _ = K ⊔ N ⊓ S''.K hI := sup_inf_assoc_of_le N hle
    _ = K := by rw [inf_comm, hS''N.inf_eq_bot, sup_bot_eq]
    _ ≤ K := le_rfl

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBasisE8FactorTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis

theorem omegaStd_eq_sum (g : ℕ) (a b : Fin g ⊕ Fin g → ℤ) :
    omegaStd a b = ∑ c, ∑ d, Out.stdSymp g (((finCongr (two_mul g)).trans finSumFinEquiv.symm).symm c)
      (((finCongr (two_mul g)).trans finSumFinEquiv.symm).symm d) * (a c * b d) := by
  set σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm with hσ
  have l : ∀ a, (σ.symm (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (σ.symm (.inr a) : ℕ) = g + a := fun _ => rfl
  have ll : ∀ i j, Out.stdSymp g (σ.symm (.inl i)) (σ.symm (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r]; split_ifs <;> omega
  have rr : ∀ i j, Out.stdSymp g (σ.symm (.inr i)) (σ.symm (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r]; split_ifs <;> omega
  have lr : ∀ i j, Out.stdSymp g (σ.symm (.inl i)) (σ.symm (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]; split_ifs <;> omega
  have rl : ∀ i j, Out.stdSymp g (σ.symm (.inr i)) (σ.symm (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]; split_ifs <;> omega
  simp only [Fintype.sum_sum_type, ll, rr, lr, rl, omegaStd, Finset.sum_sub_distrib]
  simp [sub_eq_add_neg]

theorem exists_family {N g : ℕ} (hN : Odd N) {T R : Type} [CommGroup T] [CommRing R] [IsDomain R] {z : Rˣ}
    (hz : IsPrimitiveRoot z N) (hT : ∀ x : T, x ^ N = 1)
    (hc : ∀ d : ℕ, d ∣ N → Nat.card {x : T // x ^ d = 1} = d ^ (2 * g))
    (E : Matrix (Fin 8) (Fin 8) ℤ) (hE : E.transpose = E) (hdet : E.det = 1)
    (e : (Fin 8 → T) →* (Fin 8 → T) →* Rˣ) (halt : ∀ x, e x x = 1) (hnd : ∀ x, (∀ y, e x y = 1) → x = 1)
    (hrel : ∀ s t s' t' : Fin 8 → ℤ, dotProduct s (E.mulVec t) = dotProduct s' (E.mulVec t') → ∀ p q : T,
      e (fun u => p ^ s u) (fun u => q ^ t u) = e (fun u => p ^ s' u) (fun u => q ^ t' u)) :
    ∃ b : Fin g ⊕ Fin g → T, ∀ x y : Fin 8 → (Fin g ⊕ Fin g → ℤ),
      e (fun u => ∏ c, b c ^ x u c) (fun u => ∏ c, b c ^ y u c) = z ^ ∑ u, ∑ v, E u v * omegaStd (x u) (y v) := by
  let s₀ : Fin 8 → ℤ := Pi.single 0 1
  let t₀ : Fin 8 → ℤ := E.adjugate.mulVec s₀
  have h₀ : dotProduct s₀ (E.mulVec t₀) = 1 := by
    simp only [t₀, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec]
    simp [s₀]
  have h₀' : dotProduct t₀ (E.mulVec s₀) = 1 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hE, dotProduct_comm, h₀]
  let pw : (Fin 8 → ℤ) → T →* (Fin 8 → T) := fun s =>
    MonoidHom.mk' (fun p u => p ^ s u) fun p q => funext fun u => mul_zpow p q _
  let h : T →* T →* Rˣ := ((e.comp (pw s₀)).flip.comp (pw t₀)).flip
  have hh : ∀ p q, h p q = e (fun u => p ^ s₀ u) (fun u => q ^ t₀ u) := fun _ _ => rfl
  have key : ∀ (s t : Fin 8 → ℤ) (p q : T),
      e (fun u => p ^ s u) (fun u => q ^ t u) = h p q ^ dotProduct s (E.mulVec t) := fun s t p q => by
    rw [hrel s t (dotProduct s (E.mulVec t) • s₀) t₀ (by rw [smul_dotProduct, h₀, smul_eq_mul, _root_.mul_one]), hh,
      ← MonoidHom.zpow_apply, ← map_zpow]
    congr 2
    funext u
    change p ^ (dotProduct s (E.mulVec t) * s₀ u) = (p ^ s₀ u) ^ dotProduct s (E.mulVec t)
    rw [← zpow_mul, _root_.mul_comm]
  have eskew : ∀ x y, e x y * e y x = 1 := fun x y => by
    have := halt (x * y)
    simp only [map_mul, MonoidHom.mul_apply, halt, _root_.one_mul, _root_.mul_one] at this
    first | exact this | (rw [_root_.mul_comm]; exact this)
  have halt' : ∀ p, h p p = 1 := fun p => by
    have k₁ : h p p ^ 2 = 1 := by
      have := eskew (fun u => p ^ s₀ u) (fun u => p ^ t₀ u)
      rwa [key, key, h₀, h₀', zpow_one, ← pow_two] at this
    have k₂ : h p p ^ N = 1 := by rw [← map_pow, hT, map_one]
    obtain ⟨m, rfl⟩ := hN
    rwa [pow_succ, pow_mul, k₁, one_pow, _root_.one_mul] at k₂
  have hnd' : ∀ p, (∀ q, h p q = 1) → p = 1 := fun p hp => by
    have := hnd (fun u => p ^ s₀ u) fun y => by
      have hy : y = ∏ v, fun u => y v ^ (Pi.single v 1 : Fin 8 → ℤ) u := by
        funext u
        rw [Finset.prod_apply, Finset.prod_eq_single u (fun v _ hv => by simp [Pi.single_apply, hv.symm]) (by simp)]
        simp
      rw [hy, map_prod]
      exact Finset.prod_eq_one fun v _ => by rw [key, hp, one_zpow]
    simpa [s₀] using congrFun this 0
  obtain ⟨v, hv⟩ := exists_stdSymp_of_alternating_pairing N g T R z hN.pos hz hT hc h halt' hnd'
  let σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm
  refine ⟨fun c => v (σ.symm c), fun x y => ?_⟩
  have hp : ∀ x : Fin 8 → (Fin g ⊕ Fin g → ℤ),
      (fun u => ∏ c, v (σ.symm c) ^ x u c) = ∏ c, fun u => v (σ.symm c) ^ x u c := fun x =>
    funext fun u => by rw [Finset.prod_apply]
  rw [hp, hp]
  have heval (f : (Fin g ⊕ Fin g) → ((Fin 8 → T) →* Rˣ)) (a : Fin 8 → T) :
      (∏ c, f c) a = ∏ c, f c a := by
    exact map_prod (MonoidHom.eval a) f Finset.univ
  simp only [map_prod, heval, key, hv, ← zpow_mul]
  rw [Finset.prod_comm]
  have zs : ∀ {α : Type} [Fintype α] (f : α → ℤ), ∏ a, z ^ f a = z ^ ∑ a, f a := fun f =>
    (map_prod (zpowersHom Rˣ z) (fun a => Multiplicative.ofAdd (f a)) Finset.univ).symm
  simp only [zs]
  congr 1
  simp only [omegaStd_eq_sum, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun u _ => ?_))
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun u' _ => ?_))
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [σ]
  ring

theorem exists_basis : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ N : ℕ), Odd N → ∀ (K : Type) [Field K] [IsAlgClosed K], (N : K) ≠ 0 →
  ∀ (z : Kˣ), IsPrimitiveRoot z N → ∀ (P' : PolAV (Sp K)), P'.g = 8 * gQ →
  ∀ (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (P'.A ⟶ B)), E8Fibration.IsProd pr →
  (∀ (s t s' t' : Fin 8 → ℤ), dotProduct s ((E8Fibration.e8 W).mulVec t) = dotProduct s' ((E8Fibration.e8 W).mulVec t') →
    ∀ (p q : Out.baseOver (Sp K) ⟶ B), p ^ N = 1 → q ^ N = 1 →
    ∀ (x y x' y' : Out.baseOver (Sp K) ⟶ P'.A), (∀ u, x ≫ pr u = p ^ s u) → (∀ u, y ≫ pr u = q ^ t u) →
      (∀ u, x' ≫ pr u = p ^ s' u) → (∀ u, y' ≫ pr u = q ^ t' u) →
      ∀ c, Out.WeilIs P'.A P'.L N x y c → Out.WeilIs P'.A P'.L N x' y' c) →
  ∃ b : Fin gQ ⊕ Fin gQ → (Out.baseOver (Sp K) ⟶ B), (∀ c, b c ^ N = 1) ∧
    ∀ (x y : Fin 8 → (Fin gQ ⊕ Fin gQ → ℤ)) (X Y : Out.baseOver (Sp K) ⟶ P'.A),
      (∀ u, X ≫ pr u = ∏ c, b c ^ x u c) → (∀ u, Y ≫ pr u = ∏ c, b c ^ y u c) →
      Out.WeilIs P'.A P'.L N X Y (unitOn z ^ ∑ u, ∑ v, E8Fibration.e8 W u v * omegaStd (x u) (y v)) := by
  intro W hW g N hN K _ _ hK z hz P hg B _ _ pr hpr hrel
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have : IsDomain Γ(Sp K, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have hz' : IsPrimitiveRoot (unitOn z) N :=
    hz.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)
      (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1)
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P N (Out.baseOver _)
  have hmon := hpr.1
  let φ₀ : (Out.baseOver (Sp K) ⟶ P.A) →* (Fin 8 → (Out.baseOver (Sp K) ⟶ B)) :=
    MonoidHom.mk' (fun x u => x ≫ pr u) fun x y => funext fun u => MonObj.mul_comp _ _ _
  have hφ : Function.Bijective φ₀ :=
    ⟨fun x y h => (hpr.2 _ (φ₀ y)).unique (fun u => congrFun h u) fun _ => rfl,
      fun y => (hpr.2 _ y).exists.imp fun x hx => funext hx⟩
  let φ := MulEquiv.ofBijective φ₀ hφ
  have φa : ∀ x u, φ x u = x ≫ pr u := fun _ _ => rfl
  let T : Subgroup (Out.baseOver (Sp K) ⟶ B) := (powMonoidHom N).ker
  let ψ : (Fin 8 → T) →* (Out.baseOver (Sp K) ⟶ P.A) :=
    φ.symm.toMonoidHom.comp (T.subtype.compLeft (Fin 8))
  have ψa : ∀ x u, ψ x ≫ pr u = (x u).1 := fun x u =>
    (φa _ u).symm.trans (congrFun (φ.apply_symm_apply _) u)
  have hT : ∀ x : T, x ^ N = 1 := fun x => Subtype.ext x.2
  have ψt : ∀ x, ψ x ^ N = 1 := fun x => by
    rw [← map_pow, show x ^ N = 1 from funext fun u => hT _, map_one]
  have ψs : ∀ y : Out.baseOver (Sp K) ⟶ P.A, y ^ N = 1 → ∃ x, ψ x = y := fun y hy =>
    ⟨fun u => ⟨φ y u, by
      show φ y u ^ N = 1
      rw [← Pi.pow_apply, ← map_pow, hy, map_one, Pi.one_apply]⟩, φ.symm_apply_apply y⟩
  choose w hw hw' using fun x y : Fin 8 → T => w₁ _ _ (ψt x) (ψt y)
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (by rw [map_mul]; exact w₂ _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (CommPairing.weilIs_symm P.isLB (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  let e : (Fin 8 → T) →* (Fin 8 → T) →* Γ(Sp K, ⊤)ˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x))
    fun x x' => MonoidHom.ext fun y => wl x x' y
  have hc : ∀ d : ℕ, d ∣ N → Nat.card {x : T // x ^ d = 1} = d ^ (2 * g) := fun d hd => by
    have hA : Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} = d ^ (2 * P.g) :=
      (hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd hN.pos)).2.2.2.2 K (𝟙 _) (by
        obtain ⟨e, rfl⟩ := hd
        rw [Nat.cast_mul] at hK
        exact left_ne_zero_of_mul hK)
    let F : (Fin 8 → {x : T // x ^ d = 1}) → {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} := fun x =>
      ⟨ψ fun u => (x u).1, by
        rw [← map_pow, show (fun u => (x u).1) ^ d = 1 from funext fun u => (x u).2, map_one]⟩
    have hF : Function.Bijective F := by
      refine ⟨fun x y h => funext fun u => Subtype.ext (Subtype.ext ?_), fun y => ?_⟩
      · have h' : ψ (fun u => (x u).1) = ψ fun u => (y u).1 := congrArg Subtype.val h
        rw [← ψa (fun u => (x u).1) u, h', ψa]
      · obtain ⟨x, hx⟩ := ψs y.1 (by
          obtain ⟨c, hc⟩ := hd
          rw [hc, pow_mul, y.2, one_pow])
        refine ⟨fun u => ⟨x u, Subtype.ext ?_⟩, Subtype.ext hx⟩
        show (x u).1 ^ d = 1
        rw [← ψa, hx, ← φa, ← Pi.pow_apply, ← map_pow, y.2, map_one, Pi.one_apply]
    have h := Nat.card_eq_of_bijective F hF
    rw [hA, hg, Nat.card_fun, Nat.card_fin, show 2 * (8 * g) = 2 * g * 8 by ring, pow_mul] at h
    exact Nat.pow_left_injective (by norm_num) h
  obtain ⟨b, hb⟩ := exists_family (g := g) hN hz' hT hc (E8Fibration.e8 W)
    (by simp [e8, Matrix.transpose_add, add_comm]) hW.2 e
    (fun x => (hw' _ _ _ (w₃ _ (ψt x))).symm)
    (fun x hx => by
      have h1 : ψ x = 1 := hL.weilNondeg K P N hK _ (ψt x) fun y hy => by
        obtain ⟨y, rfl⟩ := ψs y hy
        have h : w x y = 1 := hx y
        exact h ▸ hw x y
      funext u
      exact Subtype.ext (by rw [← ψa, h1, ← φa, map_one]; rfl))
    (fun s t s' t' h p q => hw' _ _ _ (hrel s t s' t' h p.1 q.1 p.2 q.2 _ _ _ _
      (fun u => ψa _ u) (fun u => ψa _ u) (fun u => ψa _ u) (fun u => ψa _ u) _ (hw _ _)))
  refine ⟨fun c => (b c).1, fun c => (b c).2, fun x y X Y hX hY => ?_⟩
  have hp : ∀ (x : Fin 8 → (Fin g ⊕ Fin g → ℤ)) (X : Out.baseOver (Sp K) ⟶ P.A),
      (∀ u, X ≫ pr u = ∏ c, (b c).1 ^ x u c) → X = ψ fun u => ∏ c, b c ^ x u c := fun x X hX =>
    hφ.1 (funext fun u => (hX u).trans (Eq.symm ((ψa _ u).trans (by simp))))
  rw [hp x X hX, hp y Y hY, ← hb x y]
  exact hw _ _

end GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorBundleRigidification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensRig

theorem oneGen_isGen' {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem eta_eq_one {S : Scheme.{0}} (B : Over S) [GrpObj B] : (η[B] : 𝟙_ (Over S) ⟶ B) = 1 := by
  show _ = toUnit _ ≫ η[B]
  rw [toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp]

theorem eSec_tensφ {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {r : ℕ} (pr : Fin r → (A ⟶ B))
    (hpr : ∀ i, IsMonHom (pr i)) (k : (Fin r × Fin r) × Fin 4) : eSec A ≫ tensφ pr k = eSec B := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  have hi : η[A] ≫ pr i = η[B] := IsMonHom.one_hom _
  have hj : η[A] ≫ pr j = η[B] := IsMonHom.one_hom _
  have key : ∀ x : A ⟶ B, η[A] ≫ x = η[B] → eSec A ≫ x.left = eSec B := fun x hx => by
    rw [eSec, eSec, ← Over.comp_left, hx]
  fin_cases m
  · refine key _ ?_
    rw [MonObj.comp_mul, hi, hj, eta_eq_one, _root_.mul_one]
  · exact key _ hi
  · exact key _ hj
  · refine key _ ?_
    rw [MonObj.comp_one, eta_eq_one]

end GlobalTheory.Mum.TensRig

open GlobalTheory.Mum.TensRig in
theorem GlobalTheory.Mum.TensRig.rig_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)), (∀ i, IsMonHom (pr i)) → ∀ (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∃ rig : LB.Gen (L'.pull (eSec A')), rig.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val (LB.pullGen L' _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' * gm (ptK η[A']) z _ (w.s (fun k => J (ptK η[A'] ≫ tensφ pr k), J' (ptK η[A']))) = 1 := by
  intro R _ _ D r W A' _ L' hL' pr hpr w hw
  have hform : FormEq (X := D.P.A.left) (Y := (𝟙_ (Over (Spec (CommRingCat.of R)))).left)
      (PEmpty.elim : PEmpty → _) PEmpty.elim
      (GlobalTheory.LamBiext.flatφ (tensφ pr) (fun _ : PUnit => eSec A'))
      (GlobalTheory.LamBiext.flatε (tensε W) (fun _ : PUnit => (1 : ℤ))) := by
    intro U _ h
    simp only [GlobalTheory.LamBiext.flatφ, GlobalTheory.LamBiext.flatε, eSec_tensφ pr hpr, _root_.one_mul, Finset.univ_eq_empty,
      Finset.prod_empty, Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε]
    simp
  obtain ⟨t, ht, htv⟩ := exists_gen D.P.isLB hform (LB.oneGen D.P.L) (oneGen_isGen' _)
  obtain ⟨a, ha, hmaps⟩ := Transport.exists_transport
    (DVR.linComb_isLB L' hL' (fun _ : PUnit => eSec A') (fun _ => 1))
    (DVR.linComb_isLB _ (DVR.linComb_isLB D.P.L D.P.isLB (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A') (fun _ => 1))
    (LB.linCombIso w (fun _ : PUnit => eSec A') (fun _ => 1)) (DVR.linCombIso_isGen w hw _ _)
    (GlobalTheory.LamBiext.nest D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t)
    (GlobalTheory.LamBiext.nest_isGen ht)
  refine ⟨a, ha, fun z J J' hJ hJ' => ?_⟩
  have hPM := (GlobalTheory.GtCubeCompare.maps_iff_pm w (fun _ : PUnit => eSec A') (fun _ => 1) a _).1 hmaps
  have hp : (toUnit (TK R)).left z ∈ LB.wchart (LB.LinComb D.P.L (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => hJ (ptK η[A'] ≫ tensφ pr k)
  have hq : (toUnit (TK R)).left z ∈ LB.wchart L' (fun _ : PUnit => eSec A') (fun _ => J' (ptK η[A'])) :=
    Set.mem_iInter.2 fun _ => hJ' (ptK η[A'])
  have E := hPM _ (toUnit (TK R)).left z _ _ hp hq
  have L1 : gm (toUnit (TK R)).left z (LB.wchart (LB.LinComb D.P.L (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)))
      ((GlobalTheory.LamBiext.nest D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t).s
        (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k))) = 1 := by
    refine (gm_res _ z (GlobalTheory.LamBiext.nest_le D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') _) hp _).trans ?_
    exact (val_of t (toUnit (TK R)).left z J (fun p => J (ptK η[A'] ≫ tensφ pr p.2))
      (fun x => congrArg J (Category.assoc _ _ _).symm)).symm.trans ((htv _ _ z J hJ).trans (val_one _))
  rw [L1, Fintype.prod_unique, zpow_one] at E
  rw [val_pull hJ' a (toUnit (TK R)).left (𝟙 _),
    val_of a _ z J' (fun _ => J' (ptK η[A'])) (fun _ => by rw [Category.id_comp]; rfl), Category.id_comp, mul_comm]
  exact E.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitExtensionDivisibleValuationForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitInputExt

theorem exists_ext_dvd_rational : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (O : Type) [CommRing O] (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∀ N : ℕ, 0 < N → ∃ (T : Formalism.L2.Pj.CDVR) (ρ : R →+* T.V) (b : O →+* T.V) (ϖ : T.V) (D' : DegData T.V (maximalIdeal T.V)), Function.Injective ρ ∧ ρ.Finite ∧ Function.Injective b ∧ Irreducible ϖ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ (∀ Q : D'.toPre.X → ℤ, ReciprocityTheory.ChartRestriction.G.DVR.QForm.IsQ D'.toPre ϖ Q → ∀ u v, (N : ℤ) ∣ ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf D'.toPre Q u v) ∧ ∀ k : ℕ, k ∣ N → ∀ q : QkPt D'.toPre (AlgebraicClosure (FractionRing T.V)) k, ∃ p : QkPt D'.toPre (FractionRing T.V) k, QkExt (algebraMap (FractionRing T.V) (AlgebraicClosure (FractionRing T.V))) p q := by
  intro R _ _ _ D O _ V₁ _ _ _ ρ₁ b₁ hV₁ iρ₁ fρ₁ lρ₁ ib₁ N hN
  obtain ⟨D₁, ⟨h₁⟩⟩ := GlobalTheory.MumPull.exists_pull R V₁ ρ₁ iρ₁ lρ₁ D
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff V₁).1 hV₁
  let T₁ : Formalism.L2.Pj.CDVR := { V := V₁ }
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V₁
  obtain ⟨T', g, ϖ, e, ig, fg, hϖ, he, hass, rat⟩ :=
    GlobalTheory.QkRationalExt.exists_cdvr_ext_rational T₁ D₁.toPre D₁.tau_bimult N hN π hπ
  have lg : IsLocalHom g := fg.to_isIntegral.isLocalHom ig
  obtain ⟨D', ⟨hD⟩⟩ := GlobalTheory.MumPull.exists_pull V₁ T'.V g ig lg D₁
  have hc : Nonempty (IsPullDeg (g.comp ρ₁) D.toPre D'.toPre) :=
    GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R V₁ T'.V ρ₁ g D.toPre D₁.toPre D'.toPre ig ⟨h₁⟩ ⟨hD⟩
  choose Q₁ hQ₁ using ReciprocityTheory.ChartRestriction.G.DVR.QForm.exists_QVal hπ D₁
  have hNe : (N : ℤ) ∣ (e : ℤ) := by exact_mod_cast he
  refine ⟨T', g.comp ρ₁, g.comp b₁, ϖ, D', ig.comp iρ₁, fg.comp fρ₁, ig.comp ib₁, hϖ, hc, ?_, ?_⟩
  · intro Q hQ u v
    have hq : ∀ y, Q y = e * Q₁ (hD.xe y) := fun y =>
      ReciprocityTheory.ChartRestriction.G.DVR.QForm.QVal_unique hϖ D' (hQ y)
        (GlobalTheory.QValPull.main T₁ T' g D₁.toPre D'.toPre hD π ϖ e ig hπ hϖ hass y _ (hQ₁ _))
    rw [ReciprocityTheory.ChartRestriction.G.DVR.QForm.bOf, hq, hq, hq]
    exact dvd_sub (dvd_sub (hNe.mul_right _) (hNe.mul_right _)) (hNe.mul_right _)
  · intro k hk
    exact rat D'.toPre hD D'.tau_bimult k hk

end GlobalTheory.TraitInputExt
end
end

