module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelOnFactorOfEighthPowerAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem levelFactor_comp {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ}
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (c : Fin n → ℤ) (u : Fin m) : π u (∏ i, P i ^ c i) = L (bas c u) := by
  let φ : Λ →+ Additive H := AddMonoidHom.mk' (fun x => Additive.ofMul (L x)) hL
  have hφ : ∀ x, L x = Additive.toMul (φ x) := fun x => rfl
  have hc : bas c u = ∑ i, c i • bas (Pi.single i 1) u := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : (Pi.single i (c i) : Fin n → ℤ) = c i • (Pi.single i 1 : Fin n → ℤ) := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [hs, map_zsmul, Pi.smul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_prod, hc, hφ, map_sum, toMul_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, hP, map_zsmul, toMul_zsmul]
  rfl

theorem levelFactor_torsion {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (ht : ∀ i, P i ^ k = 1) (x : Λ) : L x ^ k = 1 := by
  obtain ⟨c, hc⟩ : ∃ c, bas c = Pi.single u x := ⟨bas.symm (Pi.single u x), bas.apply_symm_apply _⟩
  have h1 := levelFactor_comp bas P π L hL hP c u
  rw [hc, Pi.single_eq_same] at h1
  have hk : ∀ i, (P i ^ c i) ^ k = 1 := fun i => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]
  rw [← h1, ← map_pow, ← Finset.prod_pow, Finset.prod_eq_one (fun i _ => hk i), map_one]

theorem levelFactor_bij {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (hk : 0 < k) (ht : ∀ i, P i ^ k = 1)
    (hπ : ∀ y : Fin m → H, ∃! x : G, ∀ u, π u x = y u)
    (hb : ∀ y : G, y ^ k = 1 → ∃! c : Fin n → ZMod k, (List.ofFn fun i => P i ^ (c i).val).prod = y) :
    (∀ x, L x = 1 ↔ ∃ y, x = k • y) ∧ ∀ y : H, y ^ k = 1 → ∃ x, L x = y := by
  have : NeZero k := ⟨hk.ne'⟩
  have hcomp := levelFactor_comp bas P π L hL hP
  have htor := levelFactor_torsion u bas P π L hL hP k ht
  have L0 : L 0 = 1 := mul_left_cancel (a := L 0) (by rw [← hL, add_zero, _root_.mul_one])
  have hsm : ∀ (j : ℕ) (x : Λ), L (j • x) = L x ^ j := by
    intro j x
    induction j with
    | zero => rw [zero_smul, L0, pow_zero]
    | succ j ih => rw [succ_nsmul, hL, ih, pow_succ]
  have hone : ∀ a : G, (∀ v, π v a = 1) → a = 1 := by
    intro a ha
    obtain ⟨x, -, hx⟩ := hπ (fun _ => 1)
    exact (hx a ha).trans (hx 1 (fun v => map_one _)).symm
  have hred : ∀ w : Fin n → ℤ,
      ∏ i, P i ^ w i = (List.ofFn fun i => P i ^ ((w i : ZMod k).val)).prod := by
    intro w
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_eq_zpow_emod (w i) (n := (k : ℤ)) (by rw [zpow_natCast]; exact ht i),
      ← ZMod.val_intCast, zpow_natCast]
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ : ∃ w, bas w = Pi.single u x := ⟨_, bas.apply_symm_apply _⟩
    have hg : ∏ i, P i ^ w i = 1 := hone _ fun v => by
      rw [hcomp, hw]
      by_cases hv : v = u
      · subst hv; rw [Pi.single_eq_same, hx]
      · rw [Pi.single_eq_of_ne hv, L0]
    obtain ⟨c0, -, huniq⟩ := hb 1 (one_pow _)
    have e1 := huniq (fun i => (w i : ZMod k)) ((hred w).symm.trans hg)
    have e2 := huniq 0 (by simp)
    have hdvd : ∀ i, (k : ℤ) ∣ w i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun (e1.trans e2.symm) i)
    choose w' hw' using hdvd
    have hww : w = (k : ℤ) • w' := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, hw' i]
    refine ⟨bas w' u, ?_⟩
    calc x = bas w u := by rw [hw, Pi.single_eq_same]
      _ = ((k : ℤ) • bas w') u := by rw [hww, map_zsmul]
      _ = k • bas w' u := by rw [Pi.smul_apply, natCast_zsmul]
  · rintro ⟨y, rfl⟩
    rw [hsm, htor]
  · obtain ⟨a, ha, -⟩ := hπ (Pi.mulSingle u y)
    have hak : a ^ k = 1 := hone _ fun v => by
      rw [map_pow, ha]
      by_cases hv : v = u
      · subst hv; rw [Pi.mulSingle_eq_same, hy]
      · rw [Pi.mulSingle_eq_of_ne hv, one_pow]
    obtain ⟨c, hc, -⟩ := hb a hak
    refine ⟨bas (fun i => ((c i).val : ℤ)) u, ?_⟩
    have hprod : ∏ i, P i ^ ((c i).val : ℤ) = a := by
      rw [← hc, List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => zpow_natCast _ _
    rw [← hcomp, hprod, ha, Pi.mulSingle_eq_same]

theorem level_on_factor_of_eighth_power : ∀ (h g : ℕ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), 0 < k → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → (∀ x, lev x ^ k = 1) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ S), (∀ x, (toUnit (Over.mk p) ≫ lev x = 1 ↔ ∃ y, x = k • y)) ∧ ∀ y : Over.mk p ⟶ A, y ^ k = 1 → ∃ x, toUnit _ ≫ lev x = y := by
  intro h g J bas k o _ b S s t A _ _ pr lev hk hpr huniv hlev hpt
  have hcomp : ∀ i u, t.pt i ≫ pr u = lev (bas (Pi.single i 1) u) := fun i u =>
    Over.OverMorphism.ext (hpt i u)
  have hinj : ∀ (T : Over S) (x y : T ⟶ t.A), (∀ u, x ≫ pr u = y ≫ pr u) → x = y :=
    fun T x y hxy => (huniv T (fun u => y ≫ pr u)).unique hxy (fun u => rfl)
  let cg : ∀ T : Over S, CommGroup (T ⟶ t.A) := fun T =>
    { (inferInstance : Group (T ⟶ t.A)) with
      mul_comm := fun x y => hinj T _ _ fun u => by
        have := hpr u
        rw [MonObj.mul_comp, MonObj.mul_comp, _root_.mul_comm] }
  let π : ∀ T : Over S, Fin 8 → ((T ⟶ t.A) →* (T ⟶ A)) := fun T u =>
    MonoidHom.mk' (fun x => x ≫ pr u) (fun x y => by
      have := hpr u
      exact MonObj.mul_comp x y (pr u))
  refine ⟨?_, fun K _ _ p => ?_⟩
  · letI := cg (Out.baseOver S)
    exact levelFactor_torsion (G := Out.baseOver S ⟶ t.A) (H := Out.baseOver S ⟶ A)
      (0 : Fin 8) bas t.pt (π _) lev hlev hcomp k t.torsion
  let T := Over.mk p
  letI := cg T
  let q : T ⟶ Out.baseOver S := Over.homMk p (by simp [T])
  let ρ : (Out.baseOver S ⟶ t.A) →* (T ⟶ t.A) :=
    MonoidHom.mk' (fun x => q ≫ x) (fun x y => MonObj.comp_mul q x y)
  have hq : toUnit T = q := toUnit_unique _ _
  refine levelFactor_bij (G := T ⟶ t.A) (0 : Fin 8) bas (fun i => q ≫ t.pt i) (π T)
    (fun x => toUnit T ≫ lev x) (fun x y => by rw [hlev, MonObj.comp_mul]) (fun i u => ?_) k hk
    (fun i => by
      have h1 := map_pow ρ (t.pt i) k
      rw [t.torsion, map_one] at h1
      exact h1.symm)
    (fun y => huniv T y) (fun y hy => t.bij K p y hy)
  show (q ≫ t.pt i) ≫ pr u = toUnit T ≫ lev (bas (Pi.single i 1) u)
  rw [Category.assoc, hcomp, hq]

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MinimalAndDimLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FullLevel


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.ZM.FullLevel.lft_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f) :
    LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private theorem krullDim_zeroLocus_le_of_isEmbedding {S T : Type} [CommRing S] [CommRing T]
    (f : PrimeSpectrum S → PrimeSpectrum T) (hf : Topology.IsEmbedding f) (p : PrimeSpectrum S) :
    Order.krullDim (PrimeSpectrum.zeroLocus (p.asIdeal : Set S)) ≤
      Order.krullDim (PrimeSpectrum.zeroLocus ((f p).asIdeal : Set T)) := by
  have hle : ∀ a b, f a ≤ f b ↔ a ≤ b := fun a b => by
    rw [PrimeSpectrum.le_iff_specializes, PrimeSpectrum.le_iff_specializes,
      hf.isInducing.specializes_iff]
  refine Order.krullDim_le_of_strictMono (fun a => ⟨f a.1, ?_⟩) ?_
  · have ha : p ≤ a.1 := by
      have := a.2
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at this
      exact this
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    exact (hle p a.1).2 ha
  · refine Monotone.strictMono_of_injective (fun a b hab => ?_) (fun a b hab => ?_)
    · exact (hle a.1 b.1).2 hab
    · exact Subtype.ext (hf.injective (congrArg Subtype.val hab))


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.ZM.FullLevel.dim_generic_chart {o K : Type} [CommRing o] [IsDomain o] [Field K]
    [Algebra o K] [IsFractionRing o K]
    {U : Scheme.{0}} (s : U ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp o) (d : WithBot ℕ∞)
    (h : ∀ (R : Type) [CommRing R] [Algebra o R] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ U), IsOpenImmersion x →
      x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o R) →
      ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), d ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q))
    (R : Type) [CommRing R] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)))
    [IsOpenImmersion x]
    (q : Ideal R) (hq : q ∈ minimalPrimes R) : d ≤ ringKrullDim (R ⧸ q) := by
  classical
  have hpre : IsPreimmersion (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors o)
  let pr := pullback.fst s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K))
  have hpr : Topology.IsEmbedding pr := IsPreimmersion.isEmbedding pr
  let y₀ : PrimeSpectrum R := ⟨q, hq.1.1⟩
  obtain ⟨O, hO, hOx⟩ := hpr.isInducing.isOpen_iff.1 x.isOpenEmbedding.isOpen_range
  have hyO : pr (x y₀) ∈ O := by
    have : x y₀ ∈ pr ⁻¹' O := hOx ▸ ⟨y₀, rfl⟩
    exact this
  obtain ⟨V, hV, hyV, hVO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 U.isBasis_affineOpens
    (show pr (x y₀) ∈ (⟨O, hO⟩ : TopologicalSpace.Opens U) from hyO)
  have hVa : IsAffineOpen V := hV
  let A : Type := Γ(U, V)
  let j : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ U := hVa.fromSpec
  haveI : IsOpenImmersion j := hVa.isOpenImmersion_fromSpec
  letI : Algebra o A := (Spec.preimage (j ≫ s)).hom.toAlgebra
  have hjs : j ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o A) := by
    rw [RingHom.algebraMap_toAlgebra]
    simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
  have hbound := h A j inferInstance hjs
  let e : A ⊗[o] K ≃ₐ[o] FractionRing o ⊗[o] A :=
    (Algebra.TensorProduct.comm o A K).trans
      (Algebra.TensorProduct.congr (IsLocalization.algEquiv (nonZeroDivisors o) K (FractionRing o))
        AlgEquiv.refl)
  let I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing o ⊗[o] A) ≅ pullback j pr :=
    asIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom) ≪≫ (pullbackSpecIso o A K).symm ≪≫
      (pullback.congrHom hjs rfl).symm ≪≫ (pullbackRightPullbackFstIso s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)) j).symm
  let F := I.hom ≫ pullback.snd j pr
  have hF : ∀ w, F w = pullback.snd j pr (I.hom w) := fun w => rfl
  have hrange : Set.range F ⊆ Set.range x := by
    rintro _ ⟨w, rfl⟩
    rw [← hOx]
    have hmem : pullback.snd j pr (I.hom w) ∈ Set.range (pullback.snd j pr) := ⟨_, rfl⟩
    rw [IsOpenImmersion.range_pullbackSnd] at hmem
    have hmem' : pr (pullback.snd j pr (I.hom w)) ∈ j.opensRange := hmem
    rw [hVa.opensRange_fromSpec] at hmem'
    show pr (F w) ∈ O
    rw [hF]
    exact hVO hmem'
  have hy : x y₀ ∈ Set.range F := by
    have : x y₀ ∈ Set.range (pullback.snd j pr) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      show pr (x y₀) ∈ j.opensRange
      rw [hVa.opensRange_fromSpec]
      exact hyV
    obtain ⟨p, hp⟩ := this
    refine ⟨I.inv p, ?_⟩
    show (I.inv ≫ I.hom ≫ pullback.snd j pr) p = _
    rw [Iso.inv_hom_id_assoc, hp]
  obtain ⟨z, hz⟩ := hy
  let g := IsOpenImmersion.lift x F hrange
  have hg : g ≫ x = F := IsOpenImmersion.lift_fac x F hrange
  haveI : IsOpenImmersion g := by
    haveI : IsOpenImmersion (g ≫ x) := hg ▸ inferInstance
    exact IsOpenImmersion.of_comp g x
  let gf : PrimeSpectrum (FractionRing o ⊗[o] A) → PrimeSpectrum R := fun a => g a
  have hgemb : Topology.IsEmbedding gf := g.isOpenEmbedding.isEmbedding
  have hgz : gf z = y₀ := x.isOpenEmbedding.injective (by
    show x (g z) = x y₀
    rw [← Scheme.Hom.comp_apply, hg, hz])
  have hle : ∀ a b, gf a ≤ gf b ↔ a ≤ b := fun a b => by
    rw [PrimeSpectrum.le_iff_specializes, PrimeSpectrum.le_iff_specializes,
      hgemb.isInducing.specializes_iff]
  have hzmin : z.asIdeal ∈ minimalPrimes (FractionRing o ⊗[o] A) := by
    refine ⟨⟨z.isPrime, bot_le⟩, fun p' hp' hp'le => ?_⟩
    let w : PrimeSpectrum (FractionRing o ⊗[o] A) := ⟨p', hp'.1⟩
    have hwz : w ≤ z := hp'le
    have h1 : gf w ≤ y₀ := hgz ▸ (hle w z).2 hwz
    have h2 : y₀ ≤ gf w := hq.2 ⟨(gf w).isPrime, bot_le⟩ h1
    exact (hle z w).1 (hgz ▸ h2)
  have hq' : (gf z).asIdeal = q := congrArg PrimeSpectrum.asIdeal hgz
  calc d ≤ ringKrullDim ((FractionRing o ⊗[o] A) ⧸ z.asIdeal) := hbound _ hzmin
    _ = Order.krullDim (PrimeSpectrum.zeroLocus (z.asIdeal : Set (FractionRing o ⊗[o] A))) :=
      ringKrullDim_quotient _
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus ((gf z).asIdeal : Set R)) :=
      krullDim_zeroLocus_le_of_isEmbedding gf hgemb z
    _ = ringKrullDim (R ⧸ q) := by rw [hq', ringKrullDim_quotient]


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.ZM.FullLevel.charZero_of_hom {k K : Type} [Field k] [CharZero k] [Field K]
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) : CharZero K :=
  (RingHom.charZero_iff (Spec.preimage x).hom.injective).1 inferInstance

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private theorem isNilpotent_ker_fstHom_dualNumber {K : Type} [Field K] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) := by
  refine ⟨2, le_bot_iff.1 ?_⟩
  rw [pow_two, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply] at hr hs
  rw [Ideal.mem_bot]
  ext <;> simp [hr, hs]


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.ZM.FullLevel.eq_constPt {k K : Type} [Field k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K]
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) : x = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt x := by
  have hK : CharZero K :=
    _root_.GlobalTheory.ZM.FullLevel.charZero_of_hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ x)
  haveI : Algebra.IsSeparable ℚ k := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyUnramified ℚ k := Algebra.FormallyUnramified.of_isSeparable ℚ k
  obtain ⟨φ, rfl⟩ : ∃ φ : k →+* DualNumber K, x = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ :=
    ⟨(Spec.preimage x).hom, by simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]⟩
  let ψ : k →+* DualNumber K :=
    (algebraMap K (DualNumber K)).comp ((TrivSqZeroExt.fstHom K K K).toRingHom.comp φ)
  have hψ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ := by
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, ψ, ← Spec.map_comp]; rfl
  rw [hψ]
  congr 1
  have key := Algebra.FormallyUnramified.ext (R := ℚ) (A := k) (B := DualNumber K)
    (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) isNilpotent_ker_fstHom_dualNumber
    (g₁ := φ.toRatAlgHom) (g₂ := ψ.toRatAlgHom) ?_
  · exact congrArg AlgHom.toRingHom key
  · intro a
    rw [Ideal.Quotient.eq, RingHom.mem_ker]
    simp [ψ, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.ZM.FullLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.Coord
open GlobalTheory.ZM.RepBC

theorem le_iSup_chart {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) : (⊤ : Y.Opens) ≤ iSup L.U := hL.cover.ge

theorem exists_global_unit {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {t t' : L.Gen} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, t.s j = res (le_top : L.U j ≤ ⊤) w * t'.s j := by
  let u : ∀ j, Γ(Y, L.U j)ˣ := fun j => t.s j * (t'.s j)⁻¹
  have compat : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (u i) =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (u j) := by
    intro i j
    simp only [u, map_mul, map_inv, ht i j, ht' i j, mul_inv]
    simp only [_root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
  have glue : ∀ (v : ∀ j, Γ(Y, L.U j)ˣ),
      (∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (v i) =
        res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (v j)) →
      ∃ s : Γ(Y, ⊤), ∀ j, resG Y (le_top : L.U j ≤ ⊤) s = (v j).val := by
    intro v hv
    exact (TopCat.Sheaf.existsUnique_gluing' Y.sheaf L.U ⊤ (fun _ => homOfLE le_top) (le_iSup_chart hL) _ (by
        intro i j
        exact congrArg Units.val (hv i j))).exists
  obtain ⟨s, hs⟩ := glue u compat
  have compat' : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) ((u i)⁻¹) =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) ((u j)⁻¹) := by
    intro i j
    rw [map_inv, map_inv, compat]
  obtain ⟨s', hs'⟩ := glue (fun j => (u j)⁻¹) compat'
  have hss : s * s' = 1 := by
    apply Y.sheaf.eq_of_locally_eq' L.U ⊤ (fun _ => homOfLE le_top) (le_iSup_chart hL)
    intro j
    change resG Y (le_top : L.U j ≤ ⊤) (s * s') = resG Y (le_top : L.U j ≤ ⊤) 1
    rw [map_mul, map_one, hs, hs']
    exact Units.mul_inv (u j)
  let w : Γ(Y, ⊤)ˣ := ⟨s, s', hss, by simpa [mul_comm] using hss⟩
  refine ⟨w, fun j => ?_⟩
  have hw : res (le_top : L.U j ≤ ⊤) w = u j := Units.ext (hs j)
  rw [hw]
  change t.s j = (t.s j * (t'.s j)⁻¹) * t'.s j
  simp

theorem appLE_spec {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (e : (⊤ : (Sp R').Opens) ≤ spMap φ ⁻¹ᵁ ⊤)
    (a : R) : ((spMap φ).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (φ a) := by
  have h := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  refine Eq.trans ?_ h.symm
  exact r_self (X := Sp R') (U := ⊤) le_rfl (((spMap φ).app ⊤).hom _)

variable {X : Scheme.{0}} {M : LB X} {I : Type} {th : I → M.Sec} {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : I → R}

theorem baseChange (h : SecCoord M th x v) {R' : Type} [CommRing R'] (φ : R →+* R') :
    SecCoord M th (spMap φ ≫ x) (fun i => φ (v i)) := by
  obtain ⟨τ, hτ, h⟩ := h
  refine ⟨LB.pullGen M _ _ τ (spMap φ), ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen M _ _ τ hτ _, fun i j e => ?_⟩
  have hle : (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j :=
    fun _ hy => le_pull M x j (e hy)
  have h0 := congrArg ((spMap φ).appLE _ _ hle).hom (h i j (pull_le M x j))
  rw [map_mul, appLE_appLE _ _ _ _ e, appLE_r] at h0
  refine h0.trans ?_
  congr 1
  rw [← appLE_spec φ le_top]
  exact (r_appLE (spMap φ) _ _ _).symm

theorem scale (h : SecCoord M th x v) (u : Rˣ) : SecCoord M th x (fun i => u * v i) := by
  obtain ⟨τ, hτ, h⟩ := h
  let w : Γ(Sp R, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u
  refine ⟨⟨fun j => (res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹ * τ.s j⟩, fun j j' => ?_, fun i j e => ?_⟩
  · have e1 : res (inf_le_left : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j ≤ ⊤) w) =
        res (inf_le_right : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j' ≤ ⊤) w) :=
      Units.ext ((rr _ _ _).trans (rr _ _ _).symm)
    simp only [map_mul, map_inv]
    rw [hτ j j', e1, mul_left_comm]
  · rw [h i j e, map_mul, map_mul]
    have e1 : resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u) =
      (res (le_top : (M.pull x).U j ≤ ⊤) w).val := rfl
    rw [e1]
    show _ = _ * (((res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹).val * (τ.s j).val)
    rw [_root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]

theorem unique (hM : M.IsLB) (h : SecCoord M th x v) {v' : I → R} (h' : SecCoord M th x v') :
    ∃ u : Rˣ, ∀ i, v' i = u * v i := by
  obtain ⟨τ, hτ, h⟩ := h
  obtain ⟨τ', hτ', h'⟩ := h'
  have hcov : (⊤ : (Sp R).Opens) ≤ iSup (M.pull x).U := by
    intro y _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (show x y ∈ (⊤ : X.Opens) from trivial))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
  have global : ∃ w : Γ(Sp R, ⊤)ˣ, ∀ j, τ.s j = res (le_top : (M.pull x).U j ≤ ⊤) w * τ'.s j := by
    let u : ∀ j, Γ((Sp R), (M.pull x).U j)ˣ := fun j => τ.s j * (τ'.s j)⁻¹
    have compat : ∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) (u i) =
        res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) (u j) := by
      intro i j
      simp only [u, map_mul, map_inv, hτ i j, hτ' i j, mul_inv]
      simp only [_root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
    have glue : ∀ (v : ∀ j, Γ((Sp R), (M.pull x).U j)ˣ),
        (∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) (v i) =
          res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) (v j)) →
        ∃ s : Γ((Sp R), ⊤), ∀ j, resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) s = (v j).val := by
      intro v hv
      exact (TopCat.Sheaf.existsUnique_gluing' (Sp R).sheaf (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov _ (by
          intro i j
          exact congrArg Units.val (hv i j))).exists
    obtain ⟨s, hs⟩ := glue u compat
    have compaτ' : ∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) ((u i)⁻¹) =
        res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) ((u j)⁻¹) := by
      intro i j
      rw [map_inv, map_inv, compat]
    obtain ⟨s', hs'⟩ := glue (fun j => (u j)⁻¹) compaτ'
    have hss : s * s' = 1 := by
      apply (Sp R).sheaf.eq_of_locally_eq' (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov
      intro j
      change resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) (s * s') = resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) 1
      rw [map_mul, map_one, hs, hs']
      exact Units.mul_inv (u j)
    let w : Γ((Sp R), ⊤)ˣ := ⟨s, s', hss, by simpa [mul_comm] using hss⟩
    refine ⟨w, fun j => ?_⟩
    have hw : res (le_top : (M.pull x).U j ≤ ⊤) w = u j := Units.ext (hs j)
    rw [hw]
    change τ.s j = (τ.s j * (τ'.s j)⁻¹) * τ'.s j
    simp
  obtain ⟨w, hw⟩ := global
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, fun i => ?_⟩
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v' i) =
      w.val * (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i) := by
    apply (Sp R).sheaf.eq_of_locally_eq' (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov
    intro j
    have e := (h' i j (pull_le M x j)).symm.trans (h i j (pull_le M x j))
    rw [hw j] at e
    show resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _ = resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _
    rw [map_mul]
    apply (Units.mul_left_inj (τ'.s j)).1
    refine e.trans ?_
    show _ * (resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) w.val * (τ'.s j).val) = _
    ring
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom key
  rw [map_mul] at this
  simpa using this

theorem secCoord_bc_scale_unique : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), M.IsLB → SecCoord M th x v → (∀ (R' : Type) [CommRing R'] (φ : R →+* R'), SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) ∧ (∀ u : Rˣ, SecCoord M th x (fun i => u * v i)) ∧ ∀ v', SecCoord M th x v' → ∃ u : Rˣ, ∀ i, v' i = u * v i :=
  fun _ _ _ _ _ _ _ _ hM h => ⟨fun _ _ φ => baseChange h φ, scale h, fun _ h' => unique hM h h'⟩

end GlobalTheory.ZM.Coord
end
end

