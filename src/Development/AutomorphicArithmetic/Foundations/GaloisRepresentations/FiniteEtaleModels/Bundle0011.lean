module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaH
section
set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open GlobalTheory.HeckeApprox (inAf_sub inAf_nsmul inAf_mem inAfH)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

theorem betaH_holds : BetaH := by
  intro p _ D G L h κ n hn hnp hnκ hI hκ
  set u := L.actG h with hu
  set ui := L.actG h⁻¹ with hui
  have hinv : ∀ v, ui (u v) = v := by
    intro v
    rw [hu, hui, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ v, u (ui v) = v := by
    intro v
    rw [hu, hui, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hIu : ∀ v ∈ LaHat D, u v ∈ LaHat D := hI
  set h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := κ • ui with hh₀
  have h₀app : ∀ v, h₀ v = κ • ui v := fun v => rfl
  have h₀mem : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D := by
    intro v hv
    obtain ⟨v', hv', e⟩ := hκ v hv
    rw [h₀app, ← map_nsmul, ← e, hinv]
    exact hv'
  have h₀u : ∀ v, u (h₀ v) = κ • v := by
    intro v
    rw [h₀app, map_nsmul, hinv']
  have h₀c : ∀ (c : D.O) v, h₀ (actAf D c v) = actAf D c (h₀ v) := by
    intro c v
    rw [h₀app, h₀app, hui, actG_actAf, map_nsmul]
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.lattice_endomorphism_integral_approximation p D h₀ h₀mem
  obtain ⟨k, m, hkm⟩ : ∃ k : ℕ, ∃ m : ℤ, (κ : ℤ) * k = 1 + n * m := by
    have hc : Nat.Coprime κ n := hnκ.symm
    have e := Nat.gcd_eq_gcd_ab κ n
    rw [hc.gcd_eq_one] at e
    have hn' : (0:ℤ) < n := by exact_mod_cast hn
    refine ⟨(Nat.gcdA κ n % n).toNat, -(Nat.gcdB κ n) - κ * (Nat.gcdA κ n / n), ?_⟩
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne'), Int.emod_def]
    push_cast at e
    linear_combination -e
  have hsm : ∀ {M : Type} [AddCommGroup M] (y : M), (κ * k) • y = y + n • (m • y) := by
    intro M _ y
    have : (((κ * k : ℕ) : ℤ)) • y = ((1:ℤ) + n * m) • y := by push_cast; rw [hkm]
    rw [natCast_zsmul] at this
    rw [this, add_smul, one_smul, mul_smul, natCast_zsmul]
  have key : ∀ x, ∃ v ∈ LaHat D, u (inAf D (k • φ n x)) = inAf D x + n • v := by
    intro x
    obtain ⟨w, hw, e⟩ := hφ n hn hnp x
    refine ⟨m • inAf D x - k • u w, ?_, ?_⟩
    · exact sub_mem (zsmul_mem (inAf_mem D x) _) (nsmul_mem (hIu w hw) _)
    · have e2 : inAf D (φ n x) = h₀ (inAf D x) - n • w := by rw [e]; abel
      rw [inAf_nsmul, e2, map_nsmul, map_sub, h₀u, map_nsmul, smul_sub, smul_smul, mul_comm k κ, hsm,
        smul_sub n, smul_comm n k (u w)]
      abel
  have hg : ∀ x, (k • φ n) x = k • φ n x := fun x => rfl
  refine ⟨k • φ n, ?_, ?_, ?_, ?_⟩
  · intro c x
    rw [hg, hg]
    obtain ⟨w1, hw1, e1⟩ := hφ n hn hnp (c • x)
    obtain ⟨w2, hw2, e2⟩ := hφ n hn hnp x
    have a1 : inAf D (φ n (c • x)) = h₀ (inAf D (c • x)) - n • w1 := by rw [e1]; abel
    have a2 : inAf D (φ n x) = h₀ (inAf D x) - n • w2 := by rw [e2]; abel
    have hE : inAf D (k • φ n (c • x) - c • (k • φ n x)) = n • (k • (actAf D c w2 - w1)) := by
      rw [inAf_sub, inAf_nsmul, ← actAf_inAf, inAf_nsmul, map_nsmul, a1, a2, ← actAf_inAf, h₀c, map_sub,
        map_nsmul, smul_sub, smul_sub, smul_sub, smul_sub, smul_comm k n w1, smul_comm k n (actAf D c w2)]
      abel
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _
      (nsmul_mem (sub_mem (actAf_mem_laHat D c hw2) hw1) k) hE
    exact ⟨z, by rw [← hz]; abel⟩
  · intro x z hxz
    rw [hg] at hxz
    obtain ⟨v, hv, e⟩ := key x
    rw [hxz, inAf_nsmul, map_nsmul] at e
    have hx : inAf D x = n • (u (inAf D z) - v) := by rw [smul_sub, e]; abel
    exact LatDiv.eq_nsmul_of_inAf_eq_nsmul p D x n hn hnp _ (sub_mem (hIu _ (inAf_mem D z)) hv) hx
  · intro x
    obtain ⟨y, w, hw, e⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp (u (inAf D x)) (hIu _ (inAf_mem D x))
    obtain ⟨v, hv, ev⟩ := key y
    have hd : inAf D (k • φ n y) - inAf D x = ui (n • (v - w)) := by
      rw [← hinv (inAf D (k • φ n y) - inAf D x), map_sub, ev, e]
      congr 1
      rw [smul_sub]
      abel
    have h1 : inAf D (κ • (k • φ n y - x)) = n • h₀ (v - w) := by
      rw [inAf_nsmul, inAf_sub, hd, map_nsmul, h₀app, smul_comm κ n]
    obtain ⟨z1, hz1⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp _ (h₀mem _ (sub_mem hv hw)) h1
    refine ⟨y, k • z1 - m • (k • φ n y - x), ?_⟩
    have ht := hsm (k • φ n y - x)
    rw [mul_comm κ k, ← smul_smul, hz1] at ht
    rw [hg, smul_sub, smul_comm n k z1, ht]
    abel
  · intro x
    rw [hg]
    exact key x

end UpperTheory.Gal.FiniteEtaleModels
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaLat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem gen_facts {A : Type} [CommRing A] {a : A} {n : ℕ} {𝔟 : Ideal A} (G : IsGen a n 𝔟) :
    (n : A) ∈ 𝔟 ∧ ∀ c ∈ 𝔟, ∃ d, c * a = (n : A) * d := by
  have G' : (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 = Ideal.span {(n : A)} := G
  have hle : (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 ≤ 𝔟 :=
    Ideal.mul_le.mpr fun x _ y hy => 𝔟.mul_mem_left x hy
  have hN : (n : A) ∈ 𝔟 := by
    apply hle
    rw [G']
    exact Ideal.mem_span_singleton_self _
  refine ⟨hN, fun c hc => ?_⟩
  have hmem : a * c ∈ (Ideal.span {a} ⊔ Ideal.span {(n : A)}) * 𝔟 :=
    Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) hc
  rw [G', Ideal.mem_span_singleton] at hmem
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, by rw [mul_comm]; exact hd⟩

private theorem reindex_lattice_of_ideals {A O L : Type} [CommRing A] [Ring O] [Algebra A O] [AddCommGroup L] [Module O L]
    (cancel : ∀ k : ℕ, 0 < k → ∀ x y : L, k • x = k • y → x = y)
    (𝔟₁ 𝔟₂ : Ideal A) (W₁ W₂ : Submodule O L) (n m₁ : ℕ) (a₁ a₂ : A) (hn : 0 < n) (hm : 0 < m₁) (hle : 𝔟₁ ≤ 𝔟₂)
    (hn2 : (n : A) ∈ 𝔟₂) (hc2 : ∀ c ∈ 𝔟₂, ∃ d, c * a₂ = n * d)
    (BaseTypeSubspacesMapOntoBothSides : ∀ y : L, (∃ z, algebraMap A O a₁ • y = (n * m₁) • z) ↔ y ∈ W₁)
    (PairingFactorsThroughPeriods : ∀ x : L, (∀ c ∈ 𝔟₁, ∃ z, algebraMap A O c • x = (n * m₁) • z) →
      ∃ y z, x = algebraMap A O a₁ • y + (n * m₁) • z)
    (ProjectionSandwichLength : ∀ y : L, (∃ z, algebraMap A O a₂ • y = n • z) ↔ y ∈ W₂)
    (DegreeKernelLowerBound : ∀ x : L, (∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • x = n • z) → ∃ y z, x = algebraMap A O a₂ • y + n • z)
    (g : L →+ L) (h1 : ∀ (a : O) x, ∃ z, g (a • x) = a • g x + n • z)
    (h2 : ∀ x z, g x = n • z → ∃ v, x = n • v) (h3 : ∀ x, ∃ y z, g y = x + n • z) :
    ∃ β : L → L, (∀ x y, β (x + y) - (β x + β y) ∈ W₁) ∧ (∀ (c : O) x, β (c • x) - c • β x ∈ W₁) ∧
      (∀ y, β y ∈ W₁ ↔ y ∈ W₂) ∧
      (∀ x, (∀ c ∈ 𝔟₂, algebraMap A O c • x ∈ W₁) → ∃ y, x - β y ∈ W₁) ∧
      ∀ y, ∃ z, m₁ • g (algebraMap A O a₂ • y) = algebraMap A O a₁ • β y + (n * m₁) • z := by
  have hnm : ∀ v : L, m₁ • (n • v) = (n * m₁) • v := by
    intro v
    rw [mul_comm, mul_smul]
  have memW1 : ∀ v : L, (∃ z, algebraMap A O a₁ • v = (n * m₁) • z) → v ∈ W₁ := fun v h => (BaseTypeSubspacesMapOntoBothSides v).mp h
  have ex : ∀ y : L, ∃ y' z, m₁ • g (algebraMap A O a₂ • y) = algebraMap A O a₁ • y' + (n * m₁) • z := by
    intro y
    apply PairingFactorsThroughPeriods
    intro c hc
    obtain ⟨d, hd⟩ := hc2 c (hle hc)
    obtain ⟨z, hz⟩ := h1 (algebraMap A O c) (algebraMap A O a₂ • y)
    have e1 : algebraMap A O c • algebraMap A O a₂ • y = n • (algebraMap A O d • y) := by
      rw [smul_smul, ← map_mul, hd, map_mul, map_natCast, ← smul_smul, Nat.cast_smul_eq_nsmul]
    refine ⟨g (algebraMap A O d • y) - z, ?_⟩
    rw [e1, map_nsmul] at hz
    rw [smul_comm (algebraMap A O c) m₁, eq_sub_of_add_eq hz.symm, mul_comm n m₁, mul_smul]
    simp only [smul_sub]
  choose β z0 hβ using ex
  refine ⟨β, ?_, ?_, ?_, ?_, fun y => ⟨z0 y, hβ y⟩⟩
  · intro x y
    apply memW1
    refine ⟨z0 x + z0 y - z0 (x + y), ?_⟩
    have h := hβ (x + y)
    rw [smul_add, map_add (f := _), smul_add, hβ x, hβ y] at h
    rw [smul_sub, smul_add, eq_sub_of_add_eq h.symm]
    simp only [smul_add, smul_sub]
    abel
  · intro c x
    apply memW1
    obtain ⟨w, hw⟩ := h1 c (algebraMap A O a₂ • x)
    have hc := hβ (c • x)
    have comm1 : algebraMap A O a₂ • c • x = c • algebraMap A O a₂ • x := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    have comm2 : algebraMap A O a₁ • c • β x = c • algebraMap A O a₁ • β x := by
      rw [smul_smul, smul_smul, Algebra.commutes]
    refine ⟨w - z0 (c • x) + c • z0 x, ?_⟩
    rw [comm1, hw, smul_add, hnm] at hc
    have hx' : c • (m₁ • g (algebraMap A O a₂ • x)) = c • (algebraMap A O a₁ • β x + (n * m₁) • z0 x) := by
      rw [hβ x]
    rw [smul_add, smul_comm c m₁, smul_comm c (n * m₁)] at hx'
    rw [hx'] at hc
    rw [smul_sub, comm2, eq_sub_of_add_eq hc.symm]
    simp only [smul_add, smul_sub]
    abel
  · intro y
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := (BaseTypeSubspacesMapOntoBothSides (β y)).mpr hy
      have h := hβ y
      rw [hz, ← smul_add, ← hnm] at h
      have e := cancel m₁ hm _ _ h
      obtain ⟨v, hv⟩ := h2 _ _ e
      exact (ProjectionSandwichLength y).mp ⟨v, hv⟩
    · intro hy
      obtain ⟨v, hv⟩ := (ProjectionSandwichLength y).mpr hy
      apply memW1
      refine ⟨g v - z0 y, ?_⟩
      have h := hβ y
      rw [hv, map_nsmul, hnm] at h
      rw [smul_sub, eq_sub_of_add_eq h.symm]
  · intro x hx
    have hu : ∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • (algebraMap A O a₁ • x) = (n * m₁) • z := by
      intro c hc
      obtain ⟨z, hz⟩ := (BaseTypeSubspacesMapOntoBothSides _).mpr (hx c hc)
      exact ⟨z, by rw [smul_smul, ← Algebra.commutes a₁, ← smul_smul, hz]⟩
    obtain ⟨w, hw⟩ := hu _ hn2
    rw [map_natCast, Nat.cast_smul_eq_nsmul, mul_smul] at hw
    have hu1 := cancel n hn _ _ hw
    have hw2 : ∀ c ∈ 𝔟₂, ∃ z, algebraMap A O c • w = n • z := by
      intro c hc
      obtain ⟨z, hz⟩ := hu c hc
      rw [hu1, smul_comm (algebraMap A O c) m₁ w, ← hnm] at hz
      exact ⟨z, cancel m₁ hm _ _ hz⟩
    obtain ⟨y0, z0', hy0⟩ := DegreeKernelLowerBound w hw2
    obtain ⟨y1, z1, hy1⟩ := h3 y0
    obtain ⟨z2, hz2⟩ := h1 (algebraMap A O a₂) y1
    refine ⟨y1, memW1 _ ⟨z0' - algebraMap A O a₂ • z1 - z2 + z0 y1, ?_⟩⟩
    have hb := hβ y1
    rw [hz2, hy1] at hb
    simp only [smul_add] at hb
    rw [smul_comm (algebraMap A O a₂) n z1] at hb
    simp only [hnm] at hb
    rw [smul_sub, hu1, hy0, smul_add, hnm, eq_sub_of_add_eq hb.symm]
    simp only [smul_add, smul_sub]
    abel

theorem UpperTheory.Gal.FiniteEtaleModels.betaLat_holds :
    LatGen → BetaLat := by
  intro hL q _ D 𝔟₁ 𝔟₂ n m₁ a₁ a₂ hn hm hle G1 G2 g h1 h2 h3
  have cancel : ∀ k : ℕ, 0 < k → ∀ x y : D.La, k • x = k • y → x = y := by
    intro k hk x y h
    haveI := D.freeLa
    have h' : (k : ℤ) • (x - y) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, h, sub_self]
    rcases smul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 (by exact_mod_cast hk.ne')
    · exact sub_eq_zero.mp h0
  obtain ⟨BaseTypeSubspacesMapOntoBothSides, PairingFactorsThroughPeriods⟩ := hL q D a₁ (n * m₁) 𝔟₁ (Nat.mul_pos hn hm) G1
  obtain ⟨ProjectionSandwichLength, DegreeKernelLowerBound⟩ := hL q D a₂ n 𝔟₂ hn G2
  obtain ⟨hn2, hc2⟩ := gen_facts G2
  obtain ⟨β, hadd, hlin, hker, honto, hmain⟩ :=
    reindex_lattice_of_ideals cancel 𝔟₁ 𝔟₂ (wSub D 𝔟₁ 1) (wSub D 𝔟₂ 1) n m₁ a₁ a₂ hn hm hle hn2 hc2
      BaseTypeSubspacesMapOntoBothSides PairingFactorsThroughPeriods ProjectionSandwichLength DegreeKernelLowerBound g h1 h2 h3
  exact ⟨β, ⟨hadd, hlin, hker, honto⟩, hmain⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.AGalOfKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.galOfKer_holds :
    GalOfKer := by
  intro S A B _ _ _ _ hA hB ψ ψ' κ hψ hψ' h1 h2 hκ H hfin hHψ hinj hsurj
  haveI := hA
  haveI := hB
  obtain ⟨-, haF, haE, -⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S A κ hA hκ
  obtain ⟨-, -, hbE, hbS⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S B κ hB hκ
  haveI : IsProper A.hom := IsAbelianScheme.proper
  haveI : IsProper B.hom := IsAbelianScheme.proper
  haveI : Smooth B.hom := IsAbelianScheme.smooth
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance
  haveI : IsSeparated ψ'.left := IsSeparated.of_comp ψ'.left A.hom
  haveI : LocallyOfFiniteType (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance
  haveI : LocallyOfFiniteType ψ'.left := locallyOfFiniteType_of_comp ψ'.left A.hom
  haveI : IsFinite (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haF
  haveI : Etale (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haE
  haveI : Etale (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbE
  haveI : Surjective (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbS
  haveI : FormallyUnramified ψ'.left := FormallyUnramified.of_comp ψ'.left ψ.left
  refine ⟨hfin, ?_, ?_, ?_, IsFinite.of_comp ψ.left ψ'.left, Etale.of_comp ψ.left ψ'.left,
    Surjective.of_comp ψ'.left ψ.left, ?_⟩
  · simp [Hecke.PullHecke.transl_one]
  · intro a c
    simp [Hecke.PullHecke.transl_mul]
  · intro a
    have ht : Hecke.transl (a : 𝟙_ (Over S) ⟶ A) ≫ ψ = ψ := by
      have e := Hecke.Comp.comp_transl (𝟙 A) (a : 𝟙_ (Over S) ⟶ A)
      rw [Category.id_comp] at e
      rw [e, MonObj.mul_comp, Category.id_comp, Category.assoc, hHψ a a.2, comp_one, _root_.mul_one]
    rw [← Over.comp_left, ht]
  · intro K _ _ y y' hyy
    have hz : y' ≫ A.hom = y ≫ A.hom := by
      rw [← Over.w ψ]
      simp only [← Category.assoc, hyy]
    let Y0 : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
    let Y1 : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y' hz
    have hY : Y1 ≫ ψ = Y0 ≫ ψ := by
      ext
      simp [Y0, Y1, hyy]
    have hg : (Y1 * Y0⁻¹) ≫ ψ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hY, _root_.mul_inv_cancel]
    obtain ⟨g₀, hg₀H, hgg₀⟩ := hsurj K (y ≫ A.hom) (Y1 * Y0⁻¹) hg
    have key : ∀ h : 𝟙_ (Over S) ⟶ A, (y ≫ Over.Hom.left (Hecke.transl h) = y' ↔
        toUnit (Over.mk (y ≫ A.hom)) ≫ h = Y1 * Y0⁻¹) := by
      intro h
      have e := Hecke.Comp.comp_transl Y0 h
      constructor
      · intro hh
        have e' : Y0 ≫ Hecke.transl h = Y1 := by
          ext
          simpa [Y0, Y1] using hh
        rw [e'] at e
        rw [e, mul_comm Y0, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
      · intro hh
        rw [hh, mul_comm Y1, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul] at e
        have := congrArg Over.Hom.left e
        simpa [Y0, Y1] using this
    refine ⟨⟨g₀, hg₀H⟩, (key g₀).mpr hgg₀.symm, ?_⟩
    rintro ⟨h, hH⟩ hh
    have h3 := (key h).mp hh
    apply Subtype.ext
    have h4 : toUnit (Over.mk (y ≫ A.hom)) ≫ (h * g₀⁻¹) = 1 := by
      rw [MonObj.comp_mul, GrpObj.comp_inv, h3, hgg₀, _root_.mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj K (y ≫ A.hom) _ (H.mul_mem hH (H.inv_mem hg₀H)) h4)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevRe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.levRe_holds :
    LevRe := by
  intro q _ D R _ b N 𝔟₁ 𝔟₂ β hle hR S s o lv h
  obtain ⟨h1, h2, h3, h4⟩ := id h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp only
    rw [h.congr (hR.add x y), h1]
  · intro c x
    dsimp only
    rw [h.congr (hR.lin c x), h2]
  · intro x hx
    exact h3 _ ((hR.ker x).mpr hx)
  · intro k _ _ x
    refine ⟨fun y hy => (hR.ker y).mp ((h4 k x).1 _ hy), ?_⟩
    intro g hg
    have hg₁ : ∀ c ∈ 𝔟₁ ^ 1, g ≫ o.act.act ((algebraMap (𝓞 D.F) D.O) c) = 1 := by
      intro c hc
      rw [pow_one] at hc
      exact hg c (by rw [pow_one]; exact hle hc)
    obtain ⟨y0, hy0⟩ := (h4 k x).2 g hg₁
    obtain ⟨y, hy⟩ := hR.onto y0 (by
      intro c hc
      apply (h4 k x).1
      rw [h2, ← Category.assoc, hy0]
      exact hg c (by rw [pow_one]; exact hc))
    exact ⟨y, by dsimp only; rw [← h.congr hy, hy0]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevTr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels
open GlobalTheory.UPel.HT.EtLev.HeckeLev

private theorem UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr {p : ℕ} [Fact p.Prime] {D : Datum p} {S : Scheme.{0}} {A T : Over S}
    [GrpObj A] (act : OActN D.O A) {I : Ideal (𝓞 D.F)} {n : ℕ} (hn : (n : 𝓞 D.F) ∈ I) (t : T ⟶ A)
    (h : ∀ c ∈ I, t ≫ act.act (algebraMap (𝓞 D.F) D.O c) = 1) : t ^ n = 1 := by
  have := h _ hn
  rwa [map_natCast, act_natCast, MonObj.comp_pow, Category.comp_id] at this

theorem UpperTheory.Gal.FiniteEtaleModels.levTr_holds :
    LevTr := by
  intro q _ D R _ b f c k N 𝔟 hk hq S s o o' ψ lv hT hL
  obtain ⟨e, he⟩ := hq
  obtain ⟨hψ, hact, -, hgal, -, -⟩ := hT
  obtain ⟨hadd, hlin, hkill, hgeo⟩ := hL
  haveI := hψ
  have hnI : ((q ^ e : ℕ) : 𝓞 D.F) ∈ 𝔟 := he
  have hkn : k.Coprime (q ^ e) := Nat.Coprime.pow_right e hk
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hkn
    (pow_ne_zero e (Fact.out : q.Prime).ne_zero)
  have hmod : ∀ {Q : Type} [Monoid Q] (z : Q) (n j : ℕ), z ^ n = 1 → z ^ j = z ^ (j % n) := by
    intro Q _ z n j hz
    exact pow_eq_pow_mod j hz
  have hlv0 : lv 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  obtain ⟨φ, hφm, hψφ⟩ := GlobalTheory.HomDescent.exists_desc S o.A o'.A o.A (heckeSubA o f N) ψ hψ hgal
    (𝟙 o.A ^ k) (isMonHom_idPow o.A k) (fun h hh => by
      rw [MonObj.comp_pow, Category.comp_id]
      exact HeckeAd.pow_eq_one_of_mem o f h hh)
  haveI := hφm
  haveI : Epi ψ := by
    haveI := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact Over.epi_of_epi_left ψ
  have hφψ : φ ≫ ψ = 𝟙 o'.A ^ k := by
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψφ, pow_comp_hom, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have hφact : ∀ a : D.O, φ ≫ o.act.act a = o'.act.act a ≫ φ := by
    intro a
    haveI := o.act.hom a
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψφ, ← Category.assoc, ← hact a, Category.assoc, hψφ, pow_comp_hom,
      MonObj.comp_pow, Category.id_comp, Category.comp_id]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    beta_reduce
    rw [hadd, MonObj.mul_comp]
  · intro a x
    beta_reduce
    rw [hlin, Category.assoc, hact, Category.assoc]
  · intro x hx
    beta_reduce
    rw [hkill x hx, MonObj.one_comp]
  · intro K _ _ x
    obtain ⟨hA, hB⟩ := hgeo K x
    constructor
    · intro y hy
      beta_reduce at hy
      apply hA
      have hPk : (toUnit (Over.mk x) ≫ lv y) ^ k = 1 := by
        calc (toUnit (Over.mk x) ≫ lv y) ^ k = (toUnit (Over.mk x) ≫ lv y) ≫ 𝟙 o.A ^ k := by
              rw [MonObj.comp_pow, Category.comp_id]
          _ = (toUnit (Over.mk x) ≫ lv y ≫ ψ) ≫ φ := by rw [← hψφ]; simp only [Category.assoc]
          _ = 1 := by rw [hy, MonObj.one_comp]
      have hPn : (toUnit (Over.mk x) ≫ lv y) ^ (q ^ e) = 1 :=
        UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr o.act hnI _ (fun c hc => by
          rw [Category.assoc, ← hlin,
            hkill _ (Submodule.subset_span ⟨c, by rw [pow_one]; exact hc, y, rfl⟩), MonObj.comp_one])
      calc toUnit (Over.mk x) ≫ lv y = (toUnit (Over.mk x) ≫ lv y) ^ 1 := (pow_one _).symm
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (1 % q ^ e) := hmod _ _ 1 hPn
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (k * m % q ^ e) := by rw [hm]
        _ = (toUnit (Over.mk x) ≫ lv y) ^ (k * m) := (hmod _ _ _ hPn).symm
        _ = 1 := by rw [pow_mul, hPk, one_pow]
    · intro g hg
      have hg0 : ∀ c ∈ 𝔟 ^ 1, (g ≫ φ) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
        intro c hc
        rw [Category.assoc, hφact, ← Category.assoc, hg c hc, MonObj.one_comp]
      obtain ⟨y0, hy0⟩ := hB (g ≫ φ) hg0
      have hgk : g ^ k = toUnit (Over.mk x) ≫ lv y0 ≫ ψ := by
        rw [← Category.assoc, hy0, Category.assoc, hφψ, MonObj.comp_pow, Category.comp_id]
      have hgn : g ^ (q ^ e) = 1 :=
        UpperTheory.Gal.FiniteEtaleModels.pow_one_of_killed_tr o'.act hnI g (fun c hc => hg c (by rw [pow_one]; exact hc))
      refine ⟨m • y0, ?_⟩
      show toUnit (Over.mk x) ≫ lv (m • y0) ≫ ψ = g
      rw [map_nsmul_pow lv hadd hlv0 m y0, pow_comp_hom, MonObj.comp_pow, ← hgk, ← pow_mul,
        hmod g _ _ hgn, hm, ← hmod g _ 1 hgn, pow_one]
end

