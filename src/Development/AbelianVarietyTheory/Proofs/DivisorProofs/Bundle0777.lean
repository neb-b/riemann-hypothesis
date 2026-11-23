module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPKerRepsPowFourMul
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem prod_derivWeierstrassP_kerReps_pow_four_mul :
    ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
      Even S.card →
      (∏ t ∈ S, L.derivWeierstrassP t) ^ 4 * α ^ 12 = (latticeCurve L).Δ ^ S.card := by
  intro L α S hα hst hS hev
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = L.ω₁ / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = L.ω₂ / 2 := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = L.ω₁ / (4 * α) := ⟨_, rfl⟩
  have haL : a ∉ L.lattice := ha ▸ L.ω₁_div_two_notMem_lattice
  have hbL : b ∉ L.lattice := hb ▸ L.ω₂_div_two_notMem_lattice
  have habL : a + b ∉ L.lattice := by
    intro h
    have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := 1 / 2) (β := 1 / 2)).mp
      (by convert h using 1; rw [ha, hb]; push_cast; ring)
    norm_num at this
  have ha2 : 2 * a ∈ L.lattice := by
    have : 2 * a = L.ω₁ := by rw [ha]; ring
    rw [this]; exact L.ω₁_mem_lattice
  have hb2 : 2 * b ∈ L.lattice := by
    have : 2 * b = L.ω₂ := by rw [hb]; ring
    rw [this]; exact L.ω₂_mem_lattice
  have hab2 : 2 * (a + b) ∈ L.lattice := by
    rw [mul_add]; exact add_mem ha2 hb2
  have hz2 : 2 * (α * z) ∉ L.lattice := by
    have : 2 * (α * z) = L.ω₁ / 2 := by rw [hz]; field_simp; ring
    rw [this]; exact L.ω₁_div_two_notMem_lattice
  have two : ∀ x, x ∈ L.lattice → 2 * x ∈ L.lattice := fun x hx => by
    rw [two_mul]; exact add_mem hx hx
  have hshift : ∀ c, 2 * c ∈ L.lattice → α * (z + c) ∉ L.lattice := by
    intro c hc h
    apply hz2
    have := sub_mem (two _ h) (hst _ hc)
    convert this using 1; ring
  have hz1 : α * z ∉ L.lattice := fun h => hz2 (two _ h)
  have hαc : ∀ c, 2 * c ∈ L.lattice → 2 * (α * c) ∈ L.lattice := fun c hc => by
    have := hst _ hc
    convert this using 1; ring
  have h0 := _root_.GlobalTheory.CMModel.derivWeierstrassP_mul_prod_translate_kernel L α S hα hst hS hev z hz1
  have h1 := _root_.GlobalTheory.CMModel.derivWeierstrassP_mul_prod_translate_kernel L α S hα hst hS hev (z + a) (hshift a ha2)
  have h2 := _root_.GlobalTheory.CMModel.derivWeierstrassP_mul_prod_translate_kernel L α S hα hst hS hev (z + b) (hshift b hb2)
  have h3 := _root_.GlobalTheory.CMModel.derivWeierstrassP_mul_prod_translate_kernel L α S hα hst hS hev (z + (a + b)) (hshift _ hab2)
  have hzz : 2 * z ∉ L.lattice := fun h => hz2 (hαc z h)
  have hL0 := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b z haL hbL habL ha2 hb2 hzz
  have hLt : ∀ t ∈ S, L.derivWeierstrassP (z + t) * L.derivWeierstrassP (z + a + t)
      * L.derivWeierstrassP (z + b + t) * L.derivWeierstrassP (z + (a + b) + t)
        = (latticeCurve L).Δ := by
    intro t ht
    have h2t : 2 * (z + t) ∉ L.lattice := by
      intro h
      apply hz2
      have := sub_mem (hαc _ h) (two _ (hS.1 t ht).1)
      convert this using 1; ring
    have := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b (z + t) haL hbL habL ha2 hb2 h2t
    rw [← this, add_right_comm z a t, add_right_comm z b t, add_right_comm z (a + b) t]
  have hR := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L (α * a) (α * b) (α * z)
    (fun h => haL (_root_.GlobalTheory.CMModel.mem_lattice_of_even_kerReps L α a S hα hst hS hev h ha2))
    (fun h => hbL (_root_.GlobalTheory.CMModel.mem_lattice_of_even_kerReps L α b S hα hst hS hev h hb2))
    (fun h => habL (_root_.GlobalTheory.CMModel.mem_lattice_of_even_kerReps L α (a + b) S hα hst hS hev (by rwa [mul_add]) hab2))
    (hαc a ha2) (hαc b hb2) hz2
  rw [← mul_add α a b, ← mul_add, ← mul_add, ← mul_add] at hR
  have hP : (∏ t ∈ S, L.derivWeierstrassP (z + t)) * (∏ t ∈ S, L.derivWeierstrassP (z + a + t))
      * (∏ t ∈ S, L.derivWeierstrassP (z + b + t))
      * (∏ t ∈ S, L.derivWeierstrassP (z + (a + b) + t)) = (latticeCurve L).Δ ^ S.card := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl hLt, Finset.prod_const]
  apply mul_left_cancel₀ (latticeCurve_Δ_ne_zero L)
  have hall := congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h1) h2) h3
  rw [← hP]
  nth_rewrite 1 [← hR]
  rw [← hL0]
  linear_combination -hall

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeMonicPolyLabelsSemisimpleParameter
section
noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamExists

open GlobalTheory.GoodCharsCompare

variable {p : ℕ} [Fact p.Prime]

theorem thetaOf_gen_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1)
    (n : ℕ) : GlobalTheory.GLq.thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have hp : 0 < p ^ d - 1 := g_pow_sub_pos hd
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dite_eq_left h]
  have hfin : IsOfFinOrder (L.gen d) := by
    rw [← orderOf_pos_iff, L.gen_order d hd]; exact hp
  have h1 := hfin.pow_eq_pow_iff_modEq.1 h.choose_spec
  rw [L.gen_order d hd] at h1
  have h2 : L.teich x ^ (p ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [pow_eq_pow_mod _ h2, pow_eq_pow_mod n h2]
  exact congrArg _ h1.symm

theorem exists_gen_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) (u : Tor p d) :
    ∃ n : ℕ, ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ n := by
  haveI : NeZero (p ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hu
  exact ⟨n, hn.symm⟩

theorem exists_char (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1) :
    ∃ θ : Tor p d →* ℂˣ, LabelsChar L θ x := by
  let φ : Tor p d →* ℂ :=
    { toFun := fun u => GlobalTheory.GLq.thetaOf L d x ((u : (Fbar p)ˣ) : Fbar p)
      map_one' := by
        have := thetaOf_gen_pow L hd hx 0
        simpa using this
      map_mul' := by
        intro u v
        obtain ⟨n, hn⟩ := exists_gen_pow L hd u
        obtain ⟨m, hm⟩ := exists_gen_pow L hd v
        rw [Subgroup.coe_mul, Units.val_mul, hn, hm, ← pow_add, thetaOf_gen_pow L hd hx,
          thetaOf_gen_pow L hd hx, thetaOf_gen_pow L hd hx, pow_add] }
  exact ⟨φ.toHomUnits, hx, fun u => rfl⟩

theorem minpoly_eq_of_mem {y z : Fbar p} (h : z ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) y)) :
    minpoly (ZMod p) z = minpoly (ZMod p) y :=
  (eq_minpoly (minpoly.monic (isInt y)) (minpoly.irreducible (isInt y)) h).symm

theorem self_mem (y : Fbar p) : y ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) y) :=
  mem_roots_minpoly.2 ⟨0, by simp⟩

theorem exists_rootPoly (r : ℕ) (f : (ZMod p)[X]) (hm : f.Monic) (hr : f.natDegree = r) (h0 : f.coeff 0 ≠ 0)
    (hs : Squarefree f) : ∃ (b : Fin r → Fin r) (x : Cyc b → Fbar p), IsRootPoly x f := by
  classical
  have hf := hm.ne_zero
  have hnd := (squarefree_iff hf).1 hs
  have hz0 := (coeff_zero_iff hf).1 h0
  let S := (Formalism.CyclotomicNorms.rootsBar f).toFinset
  have hS : S.card = r := by rw [Multiset.toFinset_card_of_nodup hnd, card_rootsBar, hr]
  let e : Fin r ≃ S := (Finset.equivFinOfCardEq hS).symm
  let z : Fin r → Fbar p := fun i => (e i : Fbar p)
  have zinj : Function.Injective z := Subtype.val_injective.comp e.injective
  have zmem : ∀ i, z i ∈ Formalism.CyclotomicNorms.rootsBar f := fun i => Multiset.mem_toFinset.1 (e i).2
  have zsurj : ∀ w ∈ Formalism.CyclotomicNorms.rootsBar f, ∃ i, z i = w := fun w hw =>
    ⟨e.symm ⟨w, Multiset.mem_toFinset.2 hw⟩, by simp [z]⟩
  let m : Fin r → (ZMod p)[X] := fun i => minpoly (ZMod p) (z i)
  have hsub : ∀ i w, w ∈ Formalism.CyclotomicNorms.rootsBar (m i) → w ∈ Formalism.CyclotomicNorms.rootsBar f := by
    intro i w hw
    obtain ⟨k, rfl⟩ := mem_roots_minpoly.1 hw
    rw [mem_rootsBar hf]
    exact aeval_pow_g _ _ _ ((mem_rootsBar hf).1 (zmem i))
  have hb : ∃ b : Fin r → Fin r, (∀ i, m (b i) = m i) ∧ ∀ i j, m i = m j → b i = b j := by
    refine ⟨fun i => @Function.invFun _ _ ⟨i⟩ m (m i), fun i => @Function.invFun_eq _ _ ⟨i⟩ m _ ⟨i, rfl⟩, ?_⟩
    intro i j h
    simp only [h]
  obtain ⟨b, hb1, hb2⟩ := hb
  have hbc : ∀ c : Cyc b, ∀ i, b i = c.1 ↔ m i = m c.1 := by
    rintro ⟨c, j, rfl⟩ i
    exact ⟨fun h => by rw [← hb1 i]; exact congrArg m h, fun h => hb2 _ _ (h.trans (hb1 j))⟩
  have hlen : ∀ c : Cyc b, cycLen b c = dg (z c.1) := by
    intro c
    rw [dg, ← card_rootsBar, ← Multiset.toFinset_card_of_nodup (nodup_minpoly _), cycLen, Fintype.card_subtype]
    refine Finset.card_bij (fun i _ => z i) ?_ ?_ ?_
    · intro i hi
      have h1 : m i = m c.1 := (hbc c i).1 (Finset.mem_filter.1 hi).2
      rw [Multiset.mem_toFinset]
      exact (show minpoly (ZMod p) (z i) = minpoly (ZMod p) (z c.1) from h1) ▸ self_mem (z i)
    · intro i _ j _ h
      exact zinj h
    · intro w hw
      rw [Multiset.mem_toFinset] at hw
      obtain ⟨i, rfl⟩ := zsurj w (hsub _ w hw)
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hbc c i).2 (minpoly_eq_of_mem hw)⟩, rfl⟩
  refine ⟨b, fun c => z c.1, fun c => ?_, hm, ?_⟩
  · rw [hlen]
    exact pow_dg (fun h => hz0 (h ▸ zmem _))
  · rw [Multiset.Nodup.ext hnd (Finset.univ.nodup.map ?_)]
    · intro w
      rw [Multiset.mem_map]
      constructor
      · intro hw
        obtain ⟨i, rfl⟩ := zsurj w hw
        let c : Cyc b := ⟨b i, i, rfl⟩
        have h1 : z i ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) (z c.1)) :=
          (show minpoly (ZMod p) (z i) = minpoly (ZMod p) (z c.1) from (hb1 i).symm) ▸ self_mem (z i)
        rw [← Multiset.mem_toFinset, roots_minpoly] at h1
        obtain ⟨k, hk, hk'⟩ := Finset.mem_image.1 h1
        exact ⟨⟨c, ⟨k, by rw [hlen]; exact Finset.mem_range.1 hk⟩⟩, Finset.mem_univ_val _, hk'⟩
      · rintro ⟨y, -, rfl⟩
        exact hsub y.1.1 _ (mem_roots_minpoly.2 ⟨_, rfl⟩)
    · rintro ⟨c, i⟩ ⟨c', j⟩ h
      have h' : z c.1 ^ p ^ (i : ℕ) = z c'.1 ^ p ^ (j : ℕ) := h
      have e1 := minpoly_eq_of_mem (y := z c.1) (mem_roots_minpoly.2 ⟨i, rfl⟩)
      have e2 := minpoly_eq_of_mem (y := z c'.1) (mem_roots_minpoly.2 ⟨j, rfl⟩)
      have e3 : m c.1 = m c'.1 := e1.symm.trans (h' ▸ e2)
      have e4 : c = c' := Subtype.ext (((hbc c c.1).2 rfl).symm.trans ((hbc c' c.1).2 e3))
      subst e4
      have := (frobenius_orbit_degreeOverPrimeFieldFbar (z c.1)).2 i (hlen c ▸ i.2) j (hlen c ▸ j.2) h'
      rw [Fin.ext this]

theorem param_exists : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (f : (ZMod p)[X]),
    f.Monic → f.natDegree = r → f.coeff 0 ≠ 0 → Squarefree f →
    ∃ (s : SSParam p ℂ r) (x : Cyc s.1 → Fbar p), Labels L s x f := by
  intro p _ L r f hm hr h0 hs
  obtain ⟨b, x, hx⟩ := exists_rootPoly r f hm hr h0 hs
  choose θ hθ using fun c => exists_char L (cycLen_pos b c) (hx.1 c)
  exact ⟨⟨b, θ⟩, x, hθ, hx⟩

end GlobalTheory.ParamExists

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryCubicalBundleOfDenseAbelianNormalBase
section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymCubDense

open GlobalTheory.UU

theorem gen_unique_dense {S U X Y : Scheme.{0}} [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S)
    (j : U ⟶ S) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (T : Over S) [Smooth T.hom]
    {F : Y ⟶ T.left} {p : Y ⟶ U} (hP : IsPullback F p T.hom j) (e : U ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (T.left ⟶ X)} {ε : K → ℤ} {φ' : K' → (T.left ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u (e ≫ F) y J = val u' (e ≫ F) y J)
    (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J) (hJ : Good M z J) : val u r z J = val u' r z J := by
  refine val_corr hJ (DenseCubeExt.corr_of_open hS j T hM (fun V _ k => (hF V k).symm) hu hu' fun y I hI => ?_) r
  rw [← hP.lift_fst (pullback.fst T.hom j) (pullback.snd T.hom j) pullback.condition]
  refine (val_pull hI _ _ _).symm.trans (Eq.trans ?_ (val_pull hI _ _ _))
  exact gen_unique' hM (fun V _ k => hF V (fun q => k (F ≫ q))) p e he hp (DVR.pullGen_isGen _ _ _ _ hu F)
    (DVR.pullGen_isGen _ _ _ _ hu' F)
    (fun y J hJ => (val_pull hJ _ _ _).trans ((h y J hJ).trans (val_pull hJ _ _ _).symm)) _ _ y I hI

theorem sym_cub_of_dense_abelian : ∀ {S U : Scheme.{0}} [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (j : U ⟶ S) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (F : A.left ⟶ G.left), IsGrpPullback A G j F → GlobalFnsSt → IsAbelianScheme A → ∀ (L : RigLB G) (c : CubicalStr G L) (sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), sym.IsGen → LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sym (eSec G)) (LB.oneGen L.L) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val sym (x * y).left z J * val sym (x * u).left z J * val sym (y * u).left z J = cubV c z J x y u * val sym (x * y * u).left z J * val sym x.left z J * val sym y.left z J * val sym u.left z J := by
  intro S U _ hS j _ _ _ _ G _ _ _ _ A _ _ F gp hG hA L c sym hs hr T x y u z J hJ
  have s₂ := CubeExtension.smooth_tensor G G
  have s₃ : Smooth (G3 G).hom := CubeExtension.smooth_tensor G (G ⊗ G)
  let a := x3 G 0
  let b := x3 G 1
  let d := x3 G 2
  let sy := fun p : G3 G ⟶ G => LB.pullGen L.L _ _ sym p.left
  let cu := fun p q r : G3 G ⟶ G => LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift p (lift q r)).left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ hs _
  have gc : ∀ p q r, (cu p q r).IsGen := fun p q r => DVR.pullGen_isGen _ _ _ _ c.isGen _
  have vs : ∀ {T' : Over S} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good L.L z J → ∀ p,
      val (sy p) σ.left z J = val sym (σ ≫ p).left z J := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (cu a⁻¹ b⁻¹ d⁻¹) (sy (a * b)))
    (sy (a * d))) (sy (b * d))
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (cu a b d)
    (sy (a * b * d))) (sy a)) (sy b)) (sy d)
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good L.L z J →
      val t₁ σ.left z J = cubV c z J (σ ≫ a)⁻¹ (σ ≫ b)⁻¹ (σ ≫ d)⁻¹ * val sym ((σ ≫ a) * (σ ≫ b)).left z J *
        val sym ((σ ≫ a) * (σ ≫ d)).left z J * val sym ((σ ≫ b) * (σ ≫ d)).left z J ∧
      val t₂ σ.left z J = cubV c z J (σ ≫ a) (σ ≫ b) (σ ≫ d) * val sym ((σ ≫ a) * (σ ≫ b) * (σ ≫ d)).left z J *
        val sym (σ ≫ a).left z J * val sym (σ ≫ b).left z J * val sym (σ ≫ d).left z J := fun σ z J hJ => by
    constructor
    · rw [← MonObj.comp_mul, ← MonObj.comp_mul, ← MonObj.comp_mul, ← GrpObj.comp_inv, ← GrpObj.comp_inv,
        ← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c σ hJ _ _ _) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))
    · rw [← MonObj.comp_mul, ← MonObj.comp_mul]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
          (val_cub c σ hJ _ _ _) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))) (vs σ hJ _))
  let e : Over.mk j ⟶ G3 G := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  have e₂ : e ≫ d = 1 := by simp [e, d, x3]
  have he : eSec (G3 A) ≫ (cubeMapOf gp).F3 = e.left := by
    rw [CubeExtension.eSec_three, GlobalTheory.NormalCubeExt.groupPullback_tripleProductMap_lift, map_one]
  let ρ : T ⟶ G3 G := lift x (lift y u)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have r₂ : ρ ≫ d = u := by simp [ρ, d, x3]
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique_dense hS j (G3 G) (NormalCubeExt.isPullback_tripleProduct_groupPullback gp) (eSec (G3 A)) (CubeExtension.eSec_comp _)
      (surjective_cube hG hA) L.isLB (fun V _ k => ?_)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gc _ _ _) (gs _))
        (gs _)) (gs _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (gc _ _ _) (gs _)) (gs _)) (gs _)) (gs _)) (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (K := ((thK ⊕ Fin 2) ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub a b d k) (prod_sym (a * b * d) k))
            (prod_sym a k)) (prod_sym b k)) (prod_sym d k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := (thK ⊕ Fin 2) ⊕ Fin 2) (K' := Fin 2) (U := V) _
          (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub a⁻¹ b⁻¹ d⁻¹ k) (prod_sym (a * b) k))
            (prod_sym (a * d) k)) (prod_sym (b * d) k)).symm)
      simp only [← mul_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · have s1 : val sym (1 : Over.mk j ⟶ G).left y I = 1 := by
        rw [one_left]
        exact (val_pull hI sym (eSec G) _).symm.trans ((val_corr hI hr _).trans (val_one _))
      rw [he]
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁, e₂]
      simp only [inv_one, _root_.mul_one, s1]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  rwa [r₀, r₁, r₂] at this

end GlobalTheory.SymCubDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroup
section
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

open MeasureTheory in
open scoped FourierTransform ContDiff in
private theorem mem_levSet_iff_unitriangular_below_r {n r : ℕ} {g : GL (Fin n) ℂ} :
    g ∈ _root_.GlobalTheory.JSW.levSet n r ↔
      ∀ i : Fin n, r ≤ (i : ℕ) →
        (∀ j < i, (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧ (g : Matrix (Fin n) (Fin n) ℂ) i i = 1 :=
  Iff.rfl

open MeasureTheory in
open scoped FourierTransform ContDiff in
private theorem mul_apply_eq_apply_of_unitriangular_index_le {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    {i : Fin n} (hA : (∀ j < i, A i j = 0) ∧ A i i = 1)
    (hB : ∀ k, i < k → ∀ j < k, B k j = 0) (j : Fin n) (hj : j ≤ i) :
    (A * B) i j = B i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hA.2, one_mul]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hA.1 k hk, zero_mul]
    · rw [hB k hk j (lt_of_le_of_lt hj hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h


open MeasureTheory in
open scoped FourierTransform ContDiff in
theorem _root_.GlobalTheory.JSW.levSet_closed_subgroup : ∀ (n r : ℕ),
    (∀ g ∈ _root_.GlobalTheory.JSW.levSet n r, ∀ h ∈ _root_.GlobalTheory.JSW.levSet n r,
      g * h ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    (∀ g ∈ _root_.GlobalTheory.JSW.levSet n r, g⁻¹ ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    (∀ u ∈ _root_.GlobalTheory.SmGL.unipB ℂ (Fin n), u ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    IsClosed (_root_.GlobalTheory.JSW.levSet n r) := by
  intro n r
  refine ⟨fun g hg h hh => ?_, fun g hg => ?_, fun u hu => ?_, ?_⟩
  · rw [mem_levSet_iff_unitriangular_below_r] at hg hh ⊢
    intro i hi
    have hrow := mul_apply_eq_apply_of_unitriangular_index_le (hg i hi) (B := (h : Matrix (Fin n) (Fin n) ℂ))
      fun k hk => (hh k (hi.trans (Fin.lt_iff_val_lt_val.mp hk).le)).1
    rw [Units.val_mul]
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [hrow j hj.le]
      exact (hh i hi).1 j hj
    · rw [hrow i le_rfl]
      exact (hh i hi).2
  · rw [mem_levSet_iff_unitriangular_below_r] at hg ⊢
    have hgh : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
      Units.mul_inv g
    have key : ∀ m : ℕ, ∀ i : Fin n, r ≤ (i : ℕ) → n - (i : ℕ) ≤ m →
        (∀ j < i, ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
          ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1 := by
      intro m
      induction m with
      | zero =>
        intro i _ hm
        have := i.isLt
        omega
      | succ m ih =>
        intro i hi hm
        have hrow := mul_apply_eq_apply_of_unitriangular_index_le (hg i hi)
          (B := ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
          fun k hk => by
            have hik := Fin.lt_iff_val_lt_val.mp hk
            exact (ih k (hi.trans hik.le) (by omega)).1
        refine ⟨fun j hj => ?_, ?_⟩
        · rw [← hrow j hj.le, hgh, Matrix.one_apply_ne hj.ne']
        · rw [← hrow i le_rfl, hgh, Matrix.one_apply_eq]
    exact fun i hi => key n i hi (Nat.sub_le _ _)
  · rw [_root_.GlobalTheory.SmGL.mem_unipB] at hu
    exact fun i _ => ⟨fun j hj => hu.1 i j hj, hu.2 i⟩
  · have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) i j :=
      fun i j => Units.continuous_val.matrix_elem i j
    have hset : _root_.GlobalTheory.JSW.levSet n r = ⋂ i : Fin n, ⋂ (_ : r ≤ (i : ℕ)),
        ((⋂ j : Fin n, ⋂ (_ : j < i), {g : GL (Fin n) ℂ | (g : Matrix (Fin n) (Fin n) ℂ) i j = 0}) ∩
          {g : GL (Fin n) ℂ | (g : Matrix (Fin n) (Fin n) ℂ) i i = 1}) := by
      ext g
      simp only [mem_levSet_iff_unitriangular_below_r, Set.mem_iInter, Set.mem_inter_iff,
        Set.mem_setOf_eq]
    rw [hset]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      (isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const).inter
        (isClosed_eq (hc i i) continuous_const)

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationPowSurj
section
open IsLocalRing

namespace GlobalTheory.LocAcycUnits

open Polynomial

theorem units_pow_surj_of_sepClosed (O : Type) [CommRing O] [HenselianLocalRing O]
    [IsSepClosed (ResidueField O)] (q : ℕ) (hq : IsUnit (q : O)) (hq0 : 0 < q) (w : Oˣ) :
    ∃ v : Oˣ, v ^ q = w := by
  first
  | exact @_root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq
  | exact _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq
  | (apply _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitPowerExistence.exists_unit_pow_eq ..)

theorem units_localization_pow_surj : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ v : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, v ^ q = u := by
  intro T O _ _ _ _ _ _ _ _ _ q hT hq hq0 hO u
  obtain ⟨_, hroot⟩ := hT
  obtain ⟨c, d, w, hc, hd, hu⟩ := GlobalTheory.T.units_localization_strictHenselian_eq_const_mul_unit T O hroot hO u
  set L := Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  have root : ∀ x : T, x ≠ 0 → ∃ y : T, y ≠ 0 ∧ y ^ q = x := by
    intro x hx
    obtain ⟨y, hy⟩ := hroot (X ^ q - C x) (monic_X_pow_sub_C _ hq0.ne')
      (by rw [natDegree_X_pow_sub_C _]; exact hq0)
    have hyq : y ^ q = x := by simpa [sub_eq_zero] using hy
    refine ⟨y, ?_, hyq⟩
    rintro rfl; exact hx (by rw [← hyq, zero_pow hq0.ne'])
  have unitOf : ∀ x : T, x ≠ 0 → IsUnit (algebraMap O L (algebraMap T O x)) := fun x hx =>
    IsLocalization.map_units L (⟨algebraMap T O x,
      Algebra.mem_algebraMapSubmonoid_of_mem (⟨x, mem_nonZeroDivisors_of_ne_zero hx⟩ :
        nonZeroDivisors T)⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  obtain ⟨c', hc', hcq⟩ := root c hc
  obtain ⟨d', hd', hdq⟩ := root d hd
  have hqO : IsUnit (q : O) := by simpa using hq.map (algebraMap T O)
  obtain ⟨w', hw'⟩ := units_pow_surj_of_sepClosed O q hqO hq0 w
  have powU : ∀ (x y : T) (hx : x ≠ 0) (hy : y ≠ 0), y ^ q = x →
      (unitOf y hy).unit ^ q = (unitOf x hx).unit := by
    intro x y hx hy hxy
    apply Units.ext
    simp [← map_pow, hxy]
  have hMw : (Units.map (algebraMap O L).toMonoidHom w') ^ q = Units.map (algebraMap O L).toMonoidHom w := by
    rw [← map_pow, hw']
  have huU : u * (unitOf d hd).unit = (unitOf c hc).unit * Units.map (algebraMap O L).toMonoidHom w := by
    apply Units.ext; simpa using hu
  refine ⟨(unitOf c' hc').unit * Units.map (algebraMap O L).toMonoidHom w' * (unitOf d' hd').unit⁻¹, ?_⟩
  rw [mul_pow, mul_pow, inv_pow, powU c c' hc hc' hcq, powU d d' hd hd' hdq, hMw, ← huU]
  group

end GlobalTheory.LocAcycUnits
end

