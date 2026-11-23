module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.FunObj
open Matrix

section Ratio
variable {G : Type*} [Group G]

def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / A.relIndex B

theorem idxRatio_eq_of_le {A B D : Subgroup G} (hD : D ≤ A ⊓ B) (h0 : D.relIndex (A ⊓ B) ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / D.relIndex B := by
  have h1 := Subgroup.relIndex_mul_relIndex D (A ⊓ B) A hD inf_le_left
  have h2 := Subgroup.relIndex_mul_relIndex D (A ⊓ B) B hD inf_le_right
  have e1 : (A ⊓ B).relIndex A = B.relIndex A := by rw [inf_comm]; exact Subgroup.inf_relIndex_right B A
  have e2 : (A ⊓ B).relIndex B = A.relIndex B := Subgroup.inf_relIndex_right A B
  rw [idxRatio, ← h1, ← h2, e1, e2]
  push_cast
  rw [mul_div_mul_left _ _ (by exact_mod_cast h0)]

theorem idxRatio_map {f : G →* G} (hf : Function.Injective f) (A B : Subgroup G) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by
  rw [idxRatio, idxRatio, Subgroup.relIndex_map_map_of_injective _ _ hf,
    Subgroup.relIndex_map_map_of_injective _ _ hf]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem relIndex_inf_ne_zero {N O C H : Subgroup G} (hO : IsOpen (O : Set G)) (hC : IsCompact (C : Set G))
    (hHN : H ≤ N) (hHC : H ≤ C) : (N ⊓ O).relIndex H ≠ 0 := by
  intro h
  have h1 : O ⊓ H ≤ N ⊓ O := fun x hx => Subgroup.mem_inf.2 ⟨hHN (Subgroup.mem_inf.1 hx).2, (Subgroup.mem_inf.1 hx).1⟩
  have h2 := Subgroup.relIndex_eq_zero_of_le_left h1 h
  rw [Subgroup.inf_relIndex_right] at h2
  exact relIndex_ne_zero_of_isOpen hO hC hHC h2

theorem idxRatio_cocycle (N : Subgroup G) {U V W : Subgroup G} (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G)) (hVo : IsOpen (V : Set G)) (hVc : IsCompact (V : Set G))
    (hWo : IsOpen (W : Set G)) (hWc : IsCompact (W : Set G)) :
    idxRatio (N ⊓ U) (N ⊓ V) * idxRatio (N ⊓ V) (N ⊓ W) = idxRatio (N ⊓ U) (N ⊓ W) := by
  have hO : IsOpen ((U ⊓ V ⊓ W : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf, Subgroup.coe_inf]; exact (hUo.inter hVo).inter hWo
  have l1 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ V) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l2 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ V) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l3 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have nV : (N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ V) ≠ 0 := relIndex_inf_ne_zero hO hVc inf_le_left inf_le_right
  have nW : (N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ W) ≠ 0 := relIndex_inf_ne_zero hO hWc inf_le_left inf_le_right
  rw [idxRatio_eq_of_le l1 (relIndex_inf_ne_zero hO hUc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)),
    idxRatio_eq_of_le l2 (relIndex_inf_ne_zero hO hVc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)),
    idxRatio_eq_of_le l3 (relIndex_inf_ne_zero hO hUc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right))]
  have nV' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ V) : ℚ) ≠ 0 := by exact_mod_cast nV
  have nW' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ W) : ℚ) ≠ 0 := by exact_mod_cast nW
  field_simp

end Ratio

section Diag
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem diagGL_mul' (d e : n → kˣ) : diagGL (d * e) = diagGL d * diagGL e :=
  Units.ext (by simp [diagonal_mul_diagonal])

theorem diagGL_inv' (d : n → kˣ) : diagGL d⁻¹ = (diagGL d)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← diagGL_mul']; exact Units.ext (by simp))

theorem conj_diagGL_InN {p : ℕ} (d : n ⊕ Fin c → kˣ) {x : GL (n ⊕ Fin c) k} (hx : InN p x) :
    InN p (MulAut.conj (diagGL d) x) := by
  intro r s hrs
  have h := hx r s hrs
  have hinv : ((diagGL d)⁻¹ : GL (n ⊕ Fin c) k).val = diagonal fun i => (((d i)⁻¹ : kˣ) : k) := rfl
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, hinv, diagGL_val, mul_diagonal, diagonal_mul, h]
  by_cases hrs' : r = s
  · subst hrs'; simp
  · simp [hrs']

theorem map_conj_diagGL_N_le (p : ℕ) (d : n ⊕ Fin c → kˣ) :
    (N k n c p).map (MulAut.conj (diagGL d)).toMonoidHom ≤ N k n c p := by
  rw [N, MonoidHom.map_closure]
  exact (Subgroup.closure_le _).2 (by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.subset_closure (conj_diagGL_InN d hx))

theorem map_conj_diagGL_symN (d : n ⊕ Fin c → kˣ) :
    (symN k n c).map (MulAut.conj (diagGL d)).toMonoidHom = symN k n c := by
  have hle : ∀ d : n ⊕ Fin c → kˣ, (symN k n c).map (MulAut.conj (diagGL d)).toMonoidHom ≤ symN k n c := by
    intro d
    rw [symN, Subgroup.map_sup]
    exact sup_le_sup (map_conj_diagGL_N_le _ d) (map_conj_diagGL_N_le _ d)
  refine le_antisymm (hle d) ?_
  have h := Subgroup.map_mono (f := (MulAut.conj (diagGL d)).toMonoidHom) (hle d⁻¹)
  have e : (MulAut.conj (diagGL d)).toMonoidHom.comp (MulAut.conj (diagGL d⁻¹)).toMonoidHom = MonoidHom.id _ := by
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply, diagGL_inv']
    group
  rwa [Subgroup.map_map, e, Subgroup.map_id] at h

end Diag

end GlobalTheory.FunObj

namespace GlobalTheory.FunObj
open Matrix

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem relIndex_congr_inf {G : Type*} [Group G] {A B L : Subgroup G} (h : A ⊓ L = B ⊓ L) :
    A.relIndex L = B.relIndex L := by
  rw [← Subgroup.inf_relIndex_right A L, h, Subgroup.inf_relIndex_right]


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invVol_eq_idxRatio (C : Subgroup (GL (n ⊕ Fin c) k)) :
    invVol C = idxRatio (symN k n c ⊓ KO k _) (symN k n c ⊓ C) := by
  rw [invVol, idxRatio, relIndex_congr_inf (A := C) (B := symN k n c ⊓ C),
    relIndex_congr_inf (A := KO k _) (B := symN k n c ⊓ KO k _)]
  · ext x; simp only [Subgroup.mem_inf]; tauto
  · ext x; simp only [Subgroup.mem_inf]; tauto

theorem isOpen_map_conj_KO (x : GL (n ⊕ Fin c) k) :
    IsOpen (((KO k (n ⊕ Fin c)).map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (GL (n ⊕ Fin c) k)) := by
  rw [Subgroup.map_equiv_eq_comap_symm']
  exact isOpen_KO.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem isCompact_map_conj_KO (x : GL (n ⊕ Fin c) k) :
    IsCompact (((KO k (n ⊕ Fin c)).map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (GL (n ⊕ Fin c) k)) :=
  isCompact_KO.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem invVol_conj_diagGL_mul (d e : n ⊕ Fin c → kˣ) :
    invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom) =
      invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) *
        invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom) := by
  have hmapN : ∀ (d : n ⊕ Fin c → kˣ) (K' : Subgroup (GL (n ⊕ Fin c) k)),
      (symN k n c ⊓ K').map (MulAut.conj (diagGL d)).toMonoidHom =
        symN k n c ⊓ K'.map (MulAut.conj (diagGL d)).toMonoidHom := by
    intro d K'
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (diagGL d)).injective, map_conj_diagGL_symN]
  have hcomp : (KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom =
      ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom).map
        (MulAut.conj (diagGL d)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, diagGL_mul']
    group
  rw [invVol_eq_idxRatio, invVol_eq_idxRatio, invVol_eq_idxRatio, hcomp,
    ← idxRatio_cocycle (symN k n c) isOpen_KO isCompact_KO (isOpen_map_conj_KO (diagGL d))
      (isCompact_map_conj_KO (diagGL d)) (hcomp ▸ isOpen_map_conj_KO (diagGL (d * e)))
      (hcomp ▸ isCompact_map_conj_KO (diagGL (d * e)))]
  congr 1
  rw [← hmapN d (KO k _), ← hmapN d ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom),
    idxRatio_map (MulAut.conj (diagGL d)).injective]

end Main

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationIndependentOfChart
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

open GlobalTheory.SecGlue

namespace GlobalTheory.SecGlue.ChartIndep

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {f g : Sp S ⟶ Y}
    (e : f = g) (hf : f ⁻¹ᵁ V = ⊤) (hg : g ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V f hf x = chartHom V g hg x := by
  subst e; rfl

theorem chartHom_comp {Y : Scheme.{0}} (V : Y.Opens) {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') (f : Sp S ⟶ Y) (hf : f ⁻¹ᵁ V = ⊤) (hgf : (spMap g ≫ f) ⁻¹ᵁ V = ⊤)
    (x : Γ(Y, V)) : chartHom V (spMap g ≫ f) hgf x = g (chartHom V f hf x) := by
  unfold chartHom
  rw [← Scheme.Hom.appLE_comp_appLE (spMap g) f V ⊤ ⊤ hf.ge le_top]
  have h1 : Scheme.Hom.appLE (spMap g) ⊤ ⊤ le_top = (spMap g).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)
  rw [h1]
  change ((Scheme.ΓSpecIso (CommRingCat.of S')).hom.hom.comp
    ((Spec.map (CommRingCat.ofHom g)).appTop.hom.comp (f.appLE V ⊤ hf.ge).hom)) x = _
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, h2]
  rfl

theorem chartHom_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    (f : Sp S ⟶ Y) (hW : f ⁻¹ᵁ W = ⊤) (hV : f ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V f hV x = chartHom W f hW (Y.presheaf.map (homOfLE hWV).op x) := by
  unfold chartHom
  rw [← Scheme.Hom.map_appLE f hW.ge (homOfLE hWV).op]
  rfl

theorem lands_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    (f : Sp S ⟶ Y) (hW : f ⁻¹ᵁ W = ⊤) : f ⁻¹ᵁ V = ⊤ :=
  top_le_iff.mp (hW.ge.trans (Scheme.Hom.preimage_mono f hWV))

theorem comb_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    {ι : Type} [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S)
    (h : IsCombIn W u c w a) : IsCombIn V u c w a := by
  obtain ⟨hu, hc, hw, hx⟩ := h
  refine ⟨lands_mono hWV u hu, lands_mono hWV c hc, fun i => lands_mono hWV (w i) (hw i), fun x => ?_⟩
  rw [chartHom_mono hWV c hc, chartHom_mono hWV u hu, hx]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartHom_mono hWV (w i) (hw i)]

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue.ChartIndep

variable {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (s : S)

noncomputable def locMap : Localization.Away s →+* Localization ((Submonoid.powers s).map q) :=
  IsLocalization.map (M := Submonoid.powers s) (S := Localization.Away s)
    (T := (Submonoid.powers s).map q) _ q (Submonoid.le_comap_map _)

theorem locMap_alg (x : S) :
    locMap q s (algebraMap S (Localization.Away s) x) =
      algebraMap T (Localization ((Submonoid.powers s).map q)) (q x) :=
  IsLocalization.map_eq (M := Submonoid.powers s) (S := Localization.Away s)
    (T := (Submonoid.powers s).map q) _ x

theorem locMap_surj (hq : Function.Surjective q) : Function.Surjective (locMap q s) :=
  IsLocalization.map_surjective_of_surjective (Submonoid.powers s) (Localization.Away s)
    (Localization ((Submonoid.powers s).map q)) hq

theorem locMap_ker (hk : RingHom.ker q ^ 2 = ⊥) : RingHom.ker (locMap q s) ^ 2 = ⊥ := by
  have hprod : ∀ a b : S, a ∈ RingHom.ker q → b ∈ RingHom.ker q → a * b = 0 := by
    intro a b ha hb
    have : a * b ∈ RingHom.ker q ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hk] at this
    exact (Submodule.mem_bot S).mp this

  have hform : ∀ x ∈ RingHom.ker (locMap q s), ∃ (k : S) (m : Submonoid.powers s),
      k ∈ RingHom.ker q ∧ x = IsLocalization.mk' (Localization.Away s) k m := by
    intro x hx
    obtain ⟨⟨k, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) x
    rw [RingHom.mem_ker] at hx
    simp only [locMap] at hx
    rw [IsLocalization.map_mk' (M := Submonoid.powers s) (S := Localization.Away s)
      (T := (Submonoid.powers s).map q), IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨m', hm'⟩, hm'k⟩ := hx
    obtain ⟨m'', hm'', rfl⟩ := Submonoid.mem_map.mp hm'
    refine ⟨m'' * k, ⟨m'', hm''⟩ * m, ?_, ?_⟩
    · rw [RingHom.mem_ker, map_mul]; exact hm'k
    · simp only
      rw [IsLocalization.mk'_eq_iff_eq]
      simp only [Submonoid.coe_mul]
      ring_nf
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨k, m, hk1, rfl⟩ := hform x hx
  obtain ⟨k', m', hk2, rfl⟩ := hform y hy
  rw [← IsLocalization.mk'_mul, hprod k k' hk1 hk2, IsLocalization.mk'_zero]
  exact Submodule.zero_mem _

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue.ChartIndep

theorem lands_loc {Y : Scheme.{0}} (W : Y.Opens) {S : Type} [CommRing S] (s : S) (f : Sp S ⟶ Y)
    (hs : ∀ p : Sp S, s ∉ p.asIdeal → p ∈ f ⁻¹ᵁ W) :
    (spMap (algebraMap S (Localization.Away s)) ≫ f) ⁻¹ᵁ W = ⊤ := by
  rw [Scheme.Hom.comp_preimage]
  refine top_le_iff.mp fun x _ => ?_
  rw [Scheme.Hom.mem_preimage]
  apply hs
  intro hx
  change s ∈ Ideal.comap (algebraMap S (Localization.Away s)) x.asIdeal at hx
  rw [Ideal.mem_comap] at hx
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.Away.algebraMap_isUnit s))

theorem eq_zero_of_loc {S : Type} [CommRing S] (D : S)
    (h : ∀ p : Ideal S, p.IsMaximal → ∃ s ∉ p, algebraMap S (Localization.Away s) D = 0) : D = 0 := by
  by_contra hD
  let I : Ideal S := LinearMap.ker (LinearMap.toSpanSingleton S S D)
  have hI : I ≠ ⊤ := by
    intro hI
    have : (1 : S) ∈ I := hI ▸ Submodule.mem_top
    simp [I] at this
    exact hD this
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsD⟩ := h p hp
  obtain ⟨⟨m, hm⟩, hmD⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ D).mp hsD
  obtain ⟨n, rfl⟩ := hm
  have : s ^ n ∈ I := by simp [I]; exact hmD
  exact hs (hp.isPrime.mem_of_pow_mem n (hIp this))

end GlobalTheory.SecGlue.ChartIndep

namespace GlobalTheory.SecGlue

open ChartIndep

theorem isCombIn_of_chart : ∀ (Y : Scheme.{0}) (V V' : Y.Opens), IsAffineOpen V → IsAffineOpen V' →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    (∀ i, spMap q ≫ w i = spMap q ≫ u) → GlobalTheory.SecGlue.IsCombIn V u c w a → u ⁻¹ᵁ V' = ⊤ →
    GlobalTheory.SecGlue.IsCombIn V' u c w a := by
  intro Y V V' hV _hV' S T _ _ q hq hk ι _ u c w a hw hcomb hu'

  have hqc : spMap q ≫ c = spMap q ≫ u := by
    have h1 := GlobalTheory.T.isAffineCombinationInChart_specMap_comp Y V S T q ι u c w a hcomb
    refine _root_.GlobalTheory.SecGlue.combIn_unique Y V hV T ι (spMap q ≫ u) _ _ (fun i => spMap q ≫ w i) (fun i => q (a i)) h1 ?_
    obtain ⟨hu1, _, hw1, _⟩ := h1
    refine ⟨hu1, hu1, hw1, fun x => ?_⟩
    have h0 : ∀ i, chartHom V (spMap q ≫ w i) (hw1 i) x - chartHom V (spMap q ≫ u) hu1 x = 0 :=
      fun i => by rw [chartHom_congr V (hw i) (hw1 i) hu1 x, sub_self]
    simp [h0]

  have hc' : c ⁻¹ᵁ V' = ⊤ := by rw [← _root_.GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero S T q hq hk Y u c hqc.symm V']; exact hu'
  have hw' : ∀ i, w i ⁻¹ᵁ V' = ⊤ := fun i => by
    rw [← _root_.GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero S T q hq hk Y u (w i) (hw i).symm V']; exact hu'
  have hWsame : ∀ W : Y.Opens, c ⁻¹ᵁ W = u ⁻¹ᵁ W ∧ ∀ i, w i ⁻¹ᵁ W = u ⁻¹ᵁ W := fun W =>
    ⟨(_root_.GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero S T q hq hk Y u c hqc.symm W).symm,
      fun i => (_root_.GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero S T q hq hk Y u (w i) (hw i).symm W).symm⟩
  obtain ⟨hu, _, _, _⟩ := hcomb
  refine ⟨hu', hc', hw', fun x => ?_⟩
  rw [← sub_eq_zero]
  apply eq_zero_of_loc
  intro p hp
  let P : Sp S := ⟨p, hp.isPrime⟩
  have hPV : u P ∈ V ⊓ V' := by
    refine ⟨(Scheme.Hom.mem_preimage u).mp ?_, (Scheme.Hom.mem_preimage u).mp ?_⟩
    · rw [hu]; trivial
    · rw [hu']; trivial
  obtain ⟨W, hWaff, hPW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y)) hPV
  obtain ⟨_, ⟨s, rfl⟩, hPs, hsW⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := S)).exists_subset_of_mem_open
    (a := P) (u := ((u ⁻¹ᵁ W : (Sp S).Opens) : Set (Sp S)))
    ((Scheme.Hom.mem_preimage u).mpr hPW) (u ⁻¹ᵁ W).isOpen
  refine ⟨s, hPs, ?_⟩
  set g := algebraMap S (Localization.Away s) with hg
  have landW : ∀ f : Sp S ⟶ Y, f ⁻¹ᵁ W = u ⁻¹ᵁ W → (spMap g ≫ f) ⁻¹ᵁ W = ⊤ := by
    intro f hf
    refine lands_loc W s f fun p hp' => ?_
    rw [hf]
    exact hsW hp'
  set qs := locMap q s
  have hsq : spMap qs ≫ spMap g =
      spMap (algebraMap T (Localization ((Submonoid.powers s).map q))) ≫ spMap q := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext y
    exact locMap_alg q s y
  have hws : ∀ i, spMap qs ≫ (spMap g ≫ w i) = spMap qs ≫ (spMap g ≫ u) := fun i => by
    rw [← Category.assoc, hsq, Category.assoc, hw i, ← Category.assoc, ← hsq, Category.assoc]
  obtain ⟨d, hd, -, -⟩ := _root_.GlobalTheory.SecGlue.CombEx.exists_comb Y W hWaff (Localization.Away s) _ qs (locMap_surj q s hq)
    (locMap_ker q s hk) ι (spMap g ≫ u) (fun i => spMap g ≫ w i) (fun i => g (a i)) (landW u rfl) hws
  have hcs := GlobalTheory.T.isAffineCombinationInChart_specMap_comp Y V S (Localization.Away s) g ι u c w a ⟨hu, by assumption, by assumption, by assumption⟩
  have hdc : d = spMap g ≫ c :=
    _root_.GlobalTheory.SecGlue.combIn_unique Y V hV _ ι _ _ _ _ _ (comb_mono (hWle.trans inf_le_left) _ _ _ _ hd) hcs
  have hV'd := comb_mono (hWle.trans inf_le_right) _ _ _ _ hd
  rw [hdc] at hV'd
  obtain ⟨h1, h2, h3, hx⟩ := hV'd
  have hxx := hx x
  have hsum : ∑ i, g (a i) * (chartHom V' (spMap g ≫ w i) (h3 i) x - chartHom V' (spMap g ≫ u) h1 x) =
      g (∑ i, a i * (chartHom V' (w i) (hw' i) x - chartHom V' u hu' x)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [chartHom_comp V' g (w i) (hw' i) (h3 i), chartHom_comp V' g u hu' h1, map_mul, map_sub]
  rw [hsum, chartHom_comp V' g c hc' h2, chartHom_comp V' g u hu' h1] at hxx
  rw [map_sub, map_add (f := _), hxx, sub_self]

end GlobalTheory.SecGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInClosureLocalizationStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosedIn_etale_genFib_of_injective : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    IsIntegrallyClosedIn (GlobalTheory.KeyOriginNoeth.closure A R D)
      (Localization (Algebra.algebraMapSubmonoid (GlobalTheory.KeyOriginNoeth.closure A R D)
        (nonZeroDivisors R))) := by
  first | (exact @GlobalTheory.KeyOriginNoeth.isIntegrallyClosedIn_closure_localization) | (exact GlobalTheory.KeyOriginNoeth.isIntegrallyClosedIn_closure_localization) | (intros; apply GlobalTheory.KeyOriginNoeth.isIntegrallyClosedIn_closure_localization  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModularFormLevelOneOfInvariantQExpansion
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ : ∀ (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (a : ℕ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[k] γ = f) → _root_.GlobalTheory.QFam.HasQ N f a → _root_.ReciprocityTheory.ChartRestriction.L1.IsMF k f := by
  intro N k f a hN hinv h
  refine ⟨{ toFun := f, slash_action_eq' := ?_, holo' := ?_, bdd_at_cusps' := ?_ },
    fun _ => rfl⟩
  · rintro _ ⟨γ, rfl⟩
    exact (ModularForm.SL_slash f γ).symm.trans (hinv γ)
  · exact h.mdifferentiable hN
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [hinv γ]
    exact (_root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN h).2

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfMonic
section
open Polynomial

namespace GlobalTheory.MonicRootRange

theorem isAlgClosed_fractionRing (T : Type) [CommRing T] [IsDomain T]
    (h : GlobalTheory.LocAcyc.AbsIntClosed T) : IsAlgClosed (FractionRing T) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors T) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors T) p
  set f := algebraMap T (FractionRing T)
  have hinj : Function.Injective f := IsFractionRing.injective T (FractionRing T)
  have hb0 : f b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hsmul : (b • p : (FractionRing T)[X]) = C (f b) * p := by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  have hn : 1 ≤ p.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
  have hdeg : q.natDegree = p.natDegree := by
    have := congrArg natDegree hq
    rwa [natDegree_map_eq_of_injective hinj, hsmul, natDegree_C_mul hb0] at this
  have hq0 : q ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hdeg; omega
  have hc0 : f q.leadingCoeff ≠ 0 := (map_ne_zero_iff f hinj).mpr (leadingCoeff_ne_zero.mpr hq0)
  obtain ⟨w, hw⟩ := h q.integralNormalization (monic_integralNormalization hq0)
    (by rw [natDegree_integralNormalization]; omega)
  refine ⟨f w / f q.leadingCoeff, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul (hdeg ▸ hn) f (f w / f q.leadingCoeff)
  rw [mul_div_cancel₀ _ hc0, eval₂_at_apply, hw, map_zero] at key
  have h2 : q.eval₂ f (f w / f q.leadingCoeff) = 0 :=
    (mul_eq_zero.mp key.symm).resolve_left (pow_ne_zero _ hc0)
  rw [← eval_map, hq, hsmul, eval_mul, eval_C] at h2
  exact (mul_eq_zero.mp h2).resolve_left hb0

end GlobalTheory.MonicRootRange
end

