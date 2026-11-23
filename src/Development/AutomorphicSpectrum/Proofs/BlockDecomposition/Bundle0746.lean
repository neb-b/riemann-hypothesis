module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftMinimalGenerators
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem not_le_hyperplane {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) (r : ℕ)
    (t e : Fin r → R) (l : Fin r) (hI : Ideal.span (Set.range t) = I)
    (hz : ∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I →
      ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hl : IsUnit (e l)) :
    ¬ I ≤ IsLocalRing.maximalIdeal R * I ⊔
      Ideal.span (Set.range fun i => e l * t i - e i * t l) := by
  intro hle
  have htl : t l ∈ I := hI ▸ Ideal.subset_span ⟨l, rfl⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (hle htl)
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hq
  simp only [smul_eq_mul] at hx
  let S : R := ∑ j, x j * e j
  let z : Fin r → R := fun i => -(x i * e l) + if i = l then 1 + S else 0
  have hsum : ∑ i, z i * t i = p := by
    have h1 : ∑ i, z i * t i = -(e l * ∑ i, x i * t i) + (1 + S) * t l := by
      simp only [z, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
      congr 1
      · congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : q = e l * ∑ i, x i * t i - S * t l := by
      rw [← hx]
      simp only [S, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    linear_combination h2 - hpq
  have hzm := hz z (hsum ▸ hp)
  have hxm : ∀ i, i ≠ l → x i ∈ IsLocalRing.maximalIdeal R := fun i hi => by
    have := hzm i
    simp only [z, if_neg hi, add_zero, neg_mem_iff] at this
    exact (Ideal.unit_mul_mem_iff_mem _ hl).1 (by rwa [mul_comm])
  have hS : S - x l * e l ∈ IsLocalRing.maximalIdeal R := by
    have : S - x l * e l = ∑ j ∈ Finset.univ.erase l, x j * e j := by
      have h5 : S = x l * e l + ∑ j ∈ Finset.univ.erase l, x j * e j :=
        (Finset.add_sum_erase _ (fun j => x j * e j) (Finset.mem_univ l)).symm
      rw [h5]
      ring
    rw [this]
    exact Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ (hxm j (Finset.ne_of_mem_erase hj))
  have h3 := hzm l
  simp only [z, if_true] at h3
  have h4 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    have : (1 : R) = (-(x l * e l) + (1 + S)) - (S - x l * e l) := by ring
    rw [this]
    exact Ideal.sub_mem _ h3 hS
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top h4

theorem corrected_compat {R B : Type} [CommRing R] [CommRing B] (c : R →+* B) (I m J : Ideal R)
    (hIm : I ≤ m) (hmI : m * I ≤ J) (r : ℕ) (t e : Fin r → R) (l : Fin r) (a' : R)
    (ha : a' * e l = 1) (ht : ∀ i, t i ∈ I) (hJ : ∀ i, e l * t i - e i * t l ∈ J)
    (ua uc g βa βc : B) (b : Fin r → B)
    (hD : ua - g * uc * (1 + ∑ i, c (t i) * b i) ∈ (m * I).map c)
    (hQ : ∑ i, c (e i) * b i - (βa - βc) ∈ m.map c) :
    ua * (1 - c (a' * t l) * βa) - g * (uc * (1 - c (a' * t l) * βc)) ∈ J.map c := by
  have hII : I * I ≤ J := (Ideal.mul_mono_left hIm).trans hmI
  have hIm' : I * m ≤ J := by rwa [mul_comm]
  have hE : c (a' * t l) ∈ I.map c := Ideal.mem_map_of_mem _ (I.mul_mem_left _ (ht l))
  have hT : ∑ i, c (t i) * b i ∈ I.map c :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ht i))
  have hTE : (∑ i, c (t i) * b i) * c (a' * t l) ∈ J.map c :=
    Ideal.map_mono hII (by rw [Ideal.map_mul]; exact Ideal.mul_mem_mul hT hE)
  have hEQ : c (a' * t l) * (∑ i, c (e i) * b i - (βa - βc)) ∈ J.map c :=
    Ideal.map_mono hIm' (by rw [Ideal.map_mul]; exact Ideal.mul_mem_mul hE hQ)
  have hP : ∑ i, c (a' * (e l * t i - e i * t l)) * b i ∈ J.map c :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem _ (J.mul_mem_left _ (hJ i)))
  have hDJ := Ideal.map_mono hmI hD
  have hT' : ∑ i, c (t i) * b i = ∑ i, c (a' * (e l * t i - e i * t l)) * b i +
      c (a' * t l) * ∑ i, c (e i) * b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : c a' * c (e l) = 1 := by rw [← map_mul, ha, map_one]
    simp only [map_mul, map_sub]
    linear_combination (-(c (t i) * b i)) * h1
  generalize hTd : ∑ i, c (t i) * b i = T at *
  generalize hPd : ∑ i, c (a' * (e l * t i - e i * t l)) * b i = P at *
  generalize hSd : ∑ i, c (e i) * b i = Sg at *
  generalize c (a' * t l) = E at *
  have key : ua * (1 - E * βa) - g * (uc * (1 - E * βc)) =
      (ua - g * uc * (1 + T)) * (1 - E * βa) +
        g * uc * (P + E * (Sg - (βa - βc)) - T * E * βa) := by
    rw [hT']; ring
  rw [key]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hDJ) (Ideal.mul_mem_left _ _
    (Ideal.sub_mem _ (Ideal.add_mem _ hP hEQ) (Ideal.mul_mem_right _ _ hTE)))

theorem exists_correction : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (I : Ideal R) (r : ℕ) (t : Fin r → R),
    Ideal.span (Set.range t) = I → I ≤ IsLocalRing.maximalIdeal R →
    (∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I → ∀ i, x i ∈ IsLocalRing.maximalIdeal R) →
    ∀ (M : LB X) (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (u w : ∀ a, Γ(X, V a))
      (b : Fin r → ∀ a c, Γ(X, V a ⊓ V c)) (e : Fin r → R) (β : ∀ a, Γ(X, V a)) (l : Fin r),
      (∀ a, u a * w a - 1 ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a)) →
      (∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
        (1 + ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * b i a c) ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a ⊓ V c)) →
      IsUnit (e l) →
      (∀ a c, ∑ i, GlobalTheory.SmallExtLift.cst s _ (e i) * b i a c - (rs X inf_le_left (β a) - rs X inf_le_right (β c)) ∈
        ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c)) →
      ∃ (J : Ideal R) (y z : ∀ a, Γ(X, V a)), ¬ I ≤ J ∧ (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
        ∀ a c, rs X inf_le_left (y a) - tr M V j hj a c * rs X inf_le_right (y c) ∈ ext s J (V a ⊓ V c) := by
  intro R _ _ X s I r t hI hIm hz M A V j hj u w b e β l huw hD hl hQ
  obtain ⟨a', ha'⟩ := hl.exists_left_inv
  have hrs : ∀ {U W : X.Opens} (h : W ≤ U) (x : R),
      rs X h (GlobalTheory.SmallExtLift.cst s U x) = GlobalTheory.SmallExtLift.cst s W x := fun {U W} h x =>
    GlobalTheory.SmallExtLift.gr_ext fun y hy => by
      rw [GlobalTheory.SmallExtLift.gr_res, GlobalTheory.SmallExtLift.gr_cst, GlobalTheory.SmallExtLift.gr_cst]
  have hmJ : IsLocalRing.maximalIdeal R * I ≤ IsLocalRing.maximalIdeal R * I ⊔
      Ideal.span (Set.range fun i => e l * t i - e i * t l) := le_sup_left
  refine ⟨IsLocalRing.maximalIdeal R * I ⊔ Ideal.span (Set.range fun i => e l * t i - e i * t l),
    fun a => u a * (1 - GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a),
    fun a => w a * (1 + GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a),
    not_le_hyperplane I r t e l hI hz hl, fun a => ?_, fun a c => ?_⟩
  · have htl : t l ∈ I := hI ▸ Ideal.subset_span ⟨l, rfl⟩
    have hE2 : GlobalTheory.SmallExtLift.cst s (V a) (a' * t l) * GlobalTheory.SmallExtLift.cst s (V a) (a' * t l) ∈
        ext s (IsLocalRing.maximalIdeal R * I ⊔
          Ideal.span (Set.range fun i => e l * t i - e i * t l)) (V a) := by
      rw [← map_mul]
      refine Ideal.mem_map_of_mem _ (hmJ ?_)
      exact Ideal.mul_mem_mul (hIm (I.mul_mem_left _ htl)) (I.mul_mem_left _ htl)
    have h1 := Ideal.map_mono hmJ (huw a)
    have key : u a * (1 - GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a) *
        (w a * (1 + GlobalTheory.SmallExtLift.cst s _ (a' * t l) * β a)) - 1 =
        (u a * w a - 1) - (u a * w a * β a * β a) * (GlobalTheory.SmallExtLift.cst s (V a) (a' * t l) *
          GlobalTheory.SmallExtLift.cst s (V a) (a' * t l)) := by ring
    rw [key]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ hE2)
  · have := corrected_compat (GlobalTheory.SmallExtLift.cst s (V a ⊓ V c)) I (IsLocalRing.maximalIdeal R) _
      hIm hmJ r t e l a' ha' (fun i => hI ▸ Ideal.subset_span ⟨i, rfl⟩)
      (fun i => Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
      (rs X inf_le_left (u a)) (rs X inf_le_right (u c)) (tr M V j hj a c)
      (rs X inf_le_left (β a)) (rs X inf_le_right (β c)) (fun i => b i a c) (hD a c) (hQ a c)
    simpa only [map_mul, map_sub, map_one, hrs] using this

end GlobalTheory.CompanionTheory.FewEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitCocycleLiftModuloMaximal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq.Cochain

theorem triple_mem {B : Type*} [CommRing B] {𝔞 𝔟 : Ideal B} (h𝔟 : 𝔟 * 𝔟 ≤ 𝔞) (h𝔞 : 𝔞 ≤ 𝔟)
    {ua uc ud wc wd g₁ g₂ g₃ h₁ h₂ h₃ : B} (hc : uc * wc - 1 ∈ 𝔞) (hd : ud * wd - 1 ∈ 𝔞)
    (e₁ : ua - g₁ * uc ∈ 𝔟) (e₂ : uc - g₂ * ud ∈ 𝔟) (hg : g₁ * g₂ = g₃)
    (i₁ : g₁ * h₁ = 1) (i₂ : g₂ * h₂ = 1) (i₃ : g₃ * h₃ = 1) :
    (ua - g₁ * uc) * h₁ * wc + (uc - g₂ * ud) * h₂ * wd - (ua - g₃ * ud) * h₃ * wd ∈ 𝔞 := by
  have hh : h₃ = h₁ * h₂ := by
    subst hg
    linear_combination (-(h₃ * g₂ * h₂)) * i₁ - h₃ * i₂ + (h₁ * h₂) * i₃
  have hm : wc - h₂ * wd ∈ 𝔟 := by
    have : wc - h₂ * wd = (wd * h₂) * (uc * wc - 1) - (wc * wd * h₂) * (uc - g₂ * ud)
        - wc * (ud * wd - 1) := by
      linear_combination (-(wc * wd * ud)) * i₂
    rw [this]
    exact 𝔟.sub_mem (𝔟.sub_mem (𝔟.mul_mem_left _ (h𝔞 hc)) (𝔟.mul_mem_left _ e₂))
      (𝔟.mul_mem_left _ (h𝔞 hd))
  have : (ua - g₁ * uc) * h₁ * wc + (uc - g₂ * ud) * h₂ * wd - (ua - g₃ * ud) * h₃ * wd =
      h₁ * ((ua - g₁ * uc) * (wc - h₂ * wd)) := by
    subst hg hh
    linear_combination ((uc - g₂ * ud) * h₂ * wd) * (-i₁)
  rw [this]
  exact 𝔞.mul_mem_left _ (h𝔟 (Ideal.mul_mem_mul e₁ hm))

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem rs_cst (s : X ⟶ Sp R) {U W : X.Opens} (h : W ≤ U) (x : R) :
    rs X h (GlobalTheory.SmallExtLift.cst s U x) = GlobalTheory.SmallExtLift.cst s W x := by
  refine GlobalTheory.SmallExtLift.gr_ext fun y hy => ?_
  have e := GlobalTheory.SmallExtLift.gr_res (𝟙 X) y h hy (GlobalTheory.SmallExtLift.cst s U x)
  exact e.trans (by rw [GlobalTheory.SmallExtLift.gr_cst, GlobalTheory.SmallExtLift.gr_cst])

theorem rs_mem_ext (s : X ⟶ Sp R) (J : Ideal R) {U W : X.Opens} (h : W ≤ U) {x : Γ(X, U)}
    (hx : x ∈ ext s J U) : rs X h x ∈ ext s J W := by
  have e : (ext s J U).map (rs X h) = ext s J W := by
    rw [ext, ext, Ideal.map_map]
    congr 1
    exact RingHom.ext fun r => rs_cst s h r
  exact e ▸ Ideal.mem_map_of_mem _ hx

theorem ext_eq_span (s : X ⟶ Sp R) {I : Ideal R} {r : ℕ} {t : Fin r → R}
    (ht : Ideal.span (Set.range t) = I) (U : X.Opens) :
    ext s I U = Ideal.span (Set.range fun i => GlobalTheory.SmallExtLift.cst s U (t i)) := by
  rw [ext, ← ht, Ideal.map_span, ← Set.range_comp]
  rfl

theorem sum_cst_rs (s : X ⟶ Sp R) {r : ℕ} (t : Fin r → R) {U W : X.Opens} (h : W ≤ U)
    (f : Fin r → Γ(X, U)) :
    ∑ i, GlobalTheory.SmallExtLift.cst s W (t i) * rs X h (f i) =
      rs X h (∑ i, GlobalTheory.SmallExtLift.cst s U (t i) * f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, rs_cst]

theorem exists_cochain : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (𝔪 I : Ideal R) (r : ℕ) (t : Fin r → R),
    Ideal.span (Set.range t) = I → I ≤ 𝔪 → ∀ (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (u w : ∀ a, Γ(X, V a)),
      (∀ a, u a * w a - 1 ∈ ext s (𝔪 * I) (V a)) →
      (∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) ∈ ext s I (V a ⊓ V c)) →
      ∃ b : Fin r → ∀ a c, Γ(X, V a ⊓ V c),
        (∀ a c d, ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * (rs X (le₁₂ V a c d) (b i a c) +
            rs X (le₂₃ V a c d) (b i c d) - rs X (le₁₃ V a c d) (b i a d)) ∈ ext s (𝔪 * I) (V a ⊓ V c ⊓ V d)) ∧
        ∀ a c, rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
          (1 + ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) * b i a c) ∈ ext s (𝔪 * I) (V a ⊓ V c) := by
  intro R _ X s 𝔪 I r t ht hI M hM A V j hj u w huw he
  have key : ∀ a c, ∃ b0 : Fin r → Γ(X, V a ⊓ V c),
      ∑ i, b0 i * GlobalTheory.SmallExtLift.cst s _ (t i) =
        rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) := by
    intro a c
    have := he a c
    rw [ext_eq_span s ht] at this
    exact (Ideal.mem_span_range_iff_exists_fun).1 this
  choose b0 hb0 using key
  have hT : ∀ a c, ∑ i, GlobalTheory.SmallExtLift.cst s _ (t i) *
      (b0 a c i * trInv M V j hj a c * rs X inf_le_right (w c)) =
      (rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
        trInv M V j hj a c * rs X inf_le_right (w c) := by
    intro a c
    rw [← hb0, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine ⟨fun i a c => b0 a c i * trInv M V j hj a c * rs X inf_le_right (w c), ?_, ?_⟩
  · intro a c d
    have h𝔟 : ∀ U : X.Opens, ext s I U * ext s I U ≤ ext s (𝔪 * I) U := fun U => by
      rw [ext, ← Ideal.map_mul]
      exact Ideal.map_mono (Ideal.mul_mono_left hI)
    have h𝔞 : ∀ U : X.Opens, ext s (𝔪 * I) U ≤ ext s I U := fun U =>
      Ideal.map_mono Ideal.mul_le_right
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_cst_rs, hT]
    have i₁ := congrArg (rs X (le₁₂ V a c d)) (tr_mul_trInv M V j hj a c)
    have i₂ := congrArg (rs X (le₂₃ V a c d)) (tr_mul_trInv M V j hj c d)
    have i₃ := congrArg (rs X (le₁₃ V a c d)) (tr_mul_trInv M V j hj a d)
    rw [map_mul, map_one] at i₁ i₂ i₃
    have hU : ∀ x {W : X.Opens} (h : W ≤ V x),
        rs X h (u x) * rs X h (w x) - 1 ∈ ext s (𝔪 * I) W := fun x W h => by
      simpa only [map_sub, map_mul, map_one] using rs_mem_ext s (𝔪 * I) h (huw x)
    have := triple_mem (h𝔟 (V a ⊓ V c ⊓ V d)) (h𝔞 _)
      (hU c (inf_le_left.trans inf_le_right)) (hU d inf_le_right)
      (by simpa only [map_sub, map_mul, GlobalTheory.AbLaw.rs_rs] using rs_mem_ext s I (le₁₂ V a c d) (he a c))
      (by simpa only [map_sub, map_mul, GlobalTheory.AbLaw.rs_rs] using rs_mem_ext s I (le₂₃ V a c d) (he c d))
      (tr_cocycle hM V j hj a c d) i₁ i₂ i₃
    simpa only [map_sub, map_mul, map_add (f := _), map_one, GlobalTheory.AbLaw.rs_rs] using this
  · intro a c
    simp only [hT]
    have hx := rs_mem_ext s (𝔪 * I) (inf_le_right : V a ⊓ V c ≤ V c) (huw c)
    rw [map_sub, map_mul, map_one] at hx
    have e : rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c) *
        (1 + (rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
          trInv M V j hj a c * rs X inf_le_right (w c)) =
        -(rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
          (rs X inf_le_right (u c) * rs X inf_le_right (w c) - 1) := by
      linear_combination (-(rs X inf_le_left (u a) - tr M V j hj a c * rs X inf_le_right (u c)) *
        rs X inf_le_right (u c) * rs X inf_le_right (w c)) * tr_mul_trInv M V j hj a c
    rw [e]
    exact Ideal.mul_mem_left _ _ hx

end GlobalTheory.CompanionTheory.FewEq.Cochain
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValSuccAbove
section
open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.HopfLe.PrismComb

def stepMap (q n : ℕ) : Fin (q + 2) →o Fin 2 :=
  ⟨fun x ↦ if (x : ℕ) < n then 0 else 1, fun a b h ↦ by
    have h' : (a : ℕ) ≤ b := h
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact Fin.zero_le _
    · omega
    · exact le_rfl⟩

theorem th_apply (q : ℕ) (i : Fin (q + 1)) (x : Fin (q + 2)) :
    th q i x = if (x : ℕ) ≤ i then 0 else 1 := by
  change (if x ≤ i.castSucc then (0 : Fin 2) else 1) = _
  simp only [Fin.le_def, Fin.val_castSucc]

theorem val_succAbove {n : ℕ} (j : Fin (n + 1)) (x : Fin n) :
    ((j.succAbove x : Fin (n + 1)) : ℕ) = if (x : ℕ) < j then (x : ℕ) else x + 1 := by
  unfold Fin.succAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

theorem val_predAbove {n : ℕ} (i : Fin n) (x : Fin (n + 1)) :
    ((Fin.predAbove i x : Fin n) : ℕ) = if (i : ℕ) < x then (x : ℕ) - 1 else x := by
  unfold Fin.predAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

theorem val_sg (q : ℕ) (i : Fin (q + 1)) (x : Fin (q + 2)) :
    ((sg q i x : Fin (q + 1)) : ℕ) = if (i : ℕ) < x then (x : ℕ) - 1 else x :=
  val_predAbove i x

theorem th_diag (q : ℕ) (i : Fin (q + 2)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom = stepMap q i := by
  ext x
  have e : ((th (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom) x =
      th (q + 1) i (i.castSucc.succAbove x) := rfl
  rw [e, th_apply]
  change _ = ((if (x : ℕ) < i then (0 : Fin 2) else 1 : Fin 2) : ℕ)
  rw [val_succAbove]
  simp only [Fin.val_castSucc]
  split_ifs <;> first | rfl | omega

theorem th_next (q : ℕ) (i : Fin (q + 2)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom = stepMap q (i + 1) := by
  ext x
  have e : ((th (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom) x =
      th (q + 1) i (i.succ.succAbove x) := rfl
  rw [e, th_apply]
  change _ = ((if (x : ℕ) < i + 1 then (0 : Fin 2) else 1 : Fin 2) : ℕ)
  rw [val_succAbove]
  simp only [Fin.val_succ]
  split_ifs <;> first | rfl | omega

theorem sg_diag (q : ℕ) (i : Fin (q + 2)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom = OrderHom.id := by
  ext x
  have e : ((sg (q + 1) i).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom) x =
      sg (q + 1) i (i.castSucc.succAbove x) := rfl
  rw [e, val_sg, val_succAbove]
  simp only [Fin.val_castSucc, OrderHom.id_coe, id_eq]
  split_ifs <;> omega

theorem sg_next (q : ℕ) (i : Fin (q + 2)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom = OrderHom.id := by
  ext x
  have e : ((sg (q + 1) i).comp (Fin.succAboveOrderEmb i.succ).toOrderHom) x =
      sg (q + 1) i (i.succ.succAbove x) := rfl
  rw [e, val_sg, val_succAbove]
  simp only [Fin.val_succ, OrderHom.id_coe, id_eq]
  split_ifs <;> omega

theorem stepMap_zero (q : ℕ) : stepMap q 0 = cst (q + 1) 1 := by
  ext x
  simp [stepMap, cst]
  rfl

theorem stepMap_top (q : ℕ) : stepMap q (q + 2) = cst (q + 1) 0 := by
  ext x
  have := x.2
  simp [stepMap, cst, this]
  rfl

theorem th_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (th (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom =
      th q (Fin.predAbove k i) := by
  ext x
  have e : ((th (q + 1) i).comp
      (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) x =
      th (q + 1) i ((i.castSucc.succAbove (i.succAbove k)).succAbove x) := rfl
  rw [e, th_apply, th_apply]
  congr 2
  simp only [val_succAbove, val_predAbove, Fin.val_castSucc, eq_iff_iff]
  split_ifs <;> omega

theorem sg_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (sg (q + 1) i).comp (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom =
      (Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i)) := by
  ext x
  have e : ((sg (q + 1) i).comp
      (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) x =
      sg (q + 1) i ((i.castSucc.succAbove (i.succAbove k)).succAbove x) := rfl
  have e' : ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) x =
      (i.succAbove k).succAbove (sg q (Fin.predAbove k i) x) := rfl
  rw [e, e']
  simp only [val_sg, val_succAbove, val_predAbove, Fin.val_castSucc]
  split_ifs <;> omega

theorem sign_off (q : ℕ) (i : Fin (q + 2)) (k : Fin (q + 1)) :
    ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc.succAbove (i.succAbove k) : Fin (q + 3)) : ℕ))) =
      -((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) + ((i.succAbove k : Fin (q + 2)) : ℕ))) := by
  simp only [val_succAbove, val_predAbove, Fin.val_castSucc]
  by_cases h : (k : ℕ) < i
  · obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨(i : ℕ) - 1, by omega⟩
    rw [if_pos h, if_pos h, if_pos (by omega), hm]
    simp [pow_add, pow_succ]
  · rw [if_neg h, if_neg (by omega), if_neg (by omega)]
    simp [pow_add, pow_succ]

def fwd (q : ℕ) (p : Fin (q + 2) × Fin (q + 1)) : Fin (q + 1) × Fin (q + 2) :=
  (Fin.predAbove p.2 p.1, p.1.succAbove p.2)

def bwd (q : ℕ) (p : Fin (q + 1) × Fin (q + 2)) : Fin (q + 2) × Fin (q + 1) :=
  (⟨if (p.2 : ℕ) ≤ p.1 then (p.1 : ℕ) + 1 else p.1, by have := p.1.2; split_ifs <;> omega⟩,
   ⟨if (p.2 : ℕ) ≤ p.1 then p.2 else (p.2 : ℕ) - 1, by have := p.1.2; have := p.2.2; split_ifs <;> omega⟩)

theorem bwd_fwd (q : ℕ) (p : Fin (q + 2) × Fin (q + 1)) : bwd q (fwd q p) = p := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;>
  · simp only [bwd, fwd, val_succAbove, val_predAbove]
    split_ifs <;> omega

theorem fwd_bwd (q : ℕ) (p : Fin (q + 1) × Fin (q + 2)) : fwd q (bwd q p) = p := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;>
  · simp only [bwd, fwd, val_succAbove, val_predAbove]
    split_ifs <;> omega

theorem prism_faces {A : Type} [AddCommGroup A] (q : ℕ)
    (B : (Fin (q + 2) →o Fin 2) → (Fin (q + 2) →o Fin (q + 2)) → A) :
    ∑ i : Fin (q + 2), ∑ j : Fin (q + 3), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
        B ((th (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom)
          ((sg (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) =
      B (cst (q + 1) 1) OrderHom.id - B (cst (q + 1) 0) OrderHom.id -
        ∑ j : Fin (q + 2), ∑ i : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
          B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i)) := by
  have h1 : ∀ i : Fin (q + 2), ∑ j : Fin (q + 3), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
        B ((th (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom)
          ((sg (q + 1) i).comp (Fin.succAboveOrderEmb j).toOrderHom) =
      (B (stepMap q i) OrderHom.id - B (stepMap q (i + 1)) OrderHom.id) -
        ∑ k : Fin (q + 1), ((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) +
            ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) := by
    intro i
    rw [Fin.sum_univ_succAbove _ i.castSucc, Fin.sum_univ_succAbove _ i,
      Fin.succAbove_castSucc_self, th_diag, sg_diag, th_next, sg_next]
    have e1 : ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc : Fin (q + 3)) : ℕ))) = 1 := by
      simp [Even.neg_one_pow, ← two_mul]
    have e2 : ((-1 : ℤ) ^ ((i : ℕ) + ((i.succ : Fin (q + 3)) : ℕ))) = -1 := by
      simp [← add_assoc, ← two_mul, pow_succ]
    rw [e1, e2, one_smul, neg_smul, one_smul]
    have e3 : ∀ k : Fin (q + 1),
        ((-1 : ℤ) ^ ((i : ℕ) + ((i.castSucc.succAbove (i.succAbove k) : Fin (q + 3)) : ℕ))) •
          B ((th (q + 1) i).comp
              (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom)
            ((sg (q + 1) i).comp
              (Fin.succAboveOrderEmb (i.castSucc.succAbove (i.succAbove k))).toOrderHom) =
        -(((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) +
            ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i)))) := by
      intro k
      rw [th_off, sg_off, sign_off, neg_smul]
    simp only [e3, Finset.sum_neg_distrib]
    abel
  have h2 : ∑ i : Fin (q + 2), (B (stepMap q i) OrderHom.id - B (stepMap q (i + 1)) OrderHom.id) =
      B (cst (q + 1) 1) OrderHom.id - B (cst (q + 1) 0) OrderHom.id := by
    rw [Fin.sum_univ_eq_sum_range (fun n ↦ B (stepMap q n) OrderHom.id - B (stepMap q (n + 1)) OrderHom.id),
      Finset.sum_range_sub', stepMap_zero, stepMap_top]
  have h3 : ∑ i : Fin (q + 2), ∑ k : Fin (q + 1),
        ((-1 : ℤ) ^ (((Fin.predAbove k i : Fin (q + 1)) : ℕ) + ((i.succAbove k : Fin (q + 2)) : ℕ))) •
          B (th q (Fin.predAbove k i))
            ((Fin.succAboveOrderEmb (i.succAbove k)).toOrderHom.comp (sg q (Fin.predAbove k i))) =
      ∑ j : Fin (q + 2), ∑ i : Fin (q + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
          B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i)) := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (q + 2))))
        (t := (Finset.univ : Finset (Fin (q + 1)))) (f := fun j i ↦ ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
          B (th q i) ((Fin.succAboveOrderEmb j).toOrderHom.comp (sg q i))),
      ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    exact Finset.sum_nbij' (fwd q) (bwd q) (fun _ _ ↦ Finset.mem_univ _) (fun _ _ ↦ Finset.mem_univ _)
      (fun p _ ↦ bwd_fwd q p) (fun p _ ↦ fwd_bwd q p) (fun _ _ ↦ rfl)
  simp only [h1, Finset.sum_sub_distrib] at h2 ⊢
  rw [h2, h3]

end GlobalTheory.CompanionTheory.HopfLe.PrismComb
end

