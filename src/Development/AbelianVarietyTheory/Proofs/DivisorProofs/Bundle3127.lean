module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelsOfChain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerSkewDimSemisimpleTwoRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3120

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatTorsionHarrisTaylorAbelian
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTTors

open GlobalTheory.IwLevel GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S : Scheme.{0}} {s : S ⟶ Sp R}

def actF (o : Obj b N s) : Out.RingAct o.A (𝓞 D.F) :=
  ⟨fun c => o.act.act (algebraMap (𝓞 D.F) D.O c), fun _ => o.act.hom _,
   by rw [map_one]; exact o.act.one,
   fun _ _ => by rw [map_mul]; exact o.act.mul _ _,
   fun _ _ => by rw [map_add (f := _)]; exact o.act.add _ _⟩

theorem killedBy_map (o : Obj b N s) (w : Ideal (𝓞 D.F)) {T : Over S} (x : T ⟶ o.A) :
    KilledBy (htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x ↔ KilledBy (actF o) w x := by
  rw [Ideal.map, killedBy_span]
  exact Set.forall_mem_image

theorem inSub_ker {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] {T : Over S} (x : T ⟶ A) :
    InSub (pullback.fst f η[B]) x ↔ x ≫ f = 1 := by
  refine ⟨?_, fun h => ⟨KerGrp.lift f x h, KerGrp.lift_fst _ _ _⟩⟩
  rintro ⟨y, rfl⟩
  rw [Category.assoc, KerGrp.fst_comp, MonObj.comp_one]

theorem comp_lift_eq_one {A : Over S} [GrpObj A] {T : Over S} (x : T ⟶ A) (a c : A ⟶ A) :
    x ≫ lift a c = 1 ↔ x ≫ a = 1 ∧ x ≫ c = 1 := by
  constructor
  · intro h
    have h1 := congrArg (· ≫ fst A A) h
    have h2 := congrArg (· ≫ snd A A) h
    simp only [Category.assoc, lift_fst, lift_snd, MonObj.one_comp] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, h1, MonObj.one_comp]
    · rw [Category.assoc, lift_snd, h2, MonObj.one_comp]

theorem killedBy_pair {A : Over S} [GrpObj A] [IsCommMonObj A] (ρ : Out.RingAct A (𝓞 D.F)) (g e : 𝓞 D.F)
    {T : Over S} (x : T ⟶ A) :
    KilledBy ρ (Ideal.span {g, e}) x ↔ x ≫ lift (ρ.act g) (ρ.act e) = 1 := by
  rw [killedBy_span, comp_lift_eq_one]
  simp

theorem htTorsion : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (w : Ideal (𝓞 D.F)), w ≠ ⊥ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A), IsMonHom i ∧ Mono i ∧ GlobalTheory.IwLevel.IsIsogDeg (toUnit K) ((Ideal.absNorm w ^ D.m) ^ D.n) ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N S s o w hw
  obtain ⟨g, e, 𝔟, hg0, he, hf, hmul, hp⟩ := GlobalTheory.T.exists_coprime_ideal_mul_eq_span_numberField D.F p (Fact.out) w hw
  have hI2 := fun c hc => GlobalTheory.T.isIsogenyOfDegree_intAction_harrisTaylor p D R b N S s o c hc
  let ρ := actF o
  have hρ : ∀ c, IsMonHom (ρ.act c) := ρ.hom

  have hgw : g ∈ w * 𝔟 := by rw [hmul]; exact Ideal.mem_span_singleton_self g
  have hgw1 : g ∈ w := Ideal.mul_le_left (I := w) (J := 𝔟) hgw
  have hgw2 : g ∈ 𝔟 := Ideal.mul_le_right (I := w) (J := 𝔟) hgw
  have hw' : w = Ideal.span {g, e} := by
    apply le_antisymm
    · intro a ha
      have hsplit : a = a * (1 - e) + a * e := by ring
      rw [hsplit]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      have h1 : a * (1 - e) ∈ w * 𝔟 := Ideal.mul_mem_mul ha hf
      rw [hmul, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      rw [← ht]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hgw1, Set.singleton_subset_iff.2 he⟩)
  have h𝔟' : 𝔟 = Ideal.span {g, 1 - e} := by
    apply le_antisymm
    · intro a ha
      have hsplit : a = e * a + a * (1 - e) := by ring
      rw [hsplit]
      refine add_mem ?_ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      have h1 : e * a ∈ w * 𝔟 := Ideal.mul_mem_mul he ha
      rw [hmul, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      rw [← ht]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨hgw2, Set.singleton_subset_iff.2 hf⟩)
  have hcop : w ⊔ 𝔟 = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 D.F) = e + (1 - e) := by ring
    rw [h1]
    exact Submodule.add_mem_sup he hf
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hmul
    exact hg0 hmul

  let f₁ : o.A ⟶ o.A ⊗ o.A := lift (ρ.act g) (ρ.act e)
  let f₂ : o.A ⟶ o.A ⊗ o.A := lift (ρ.act g) (ρ.act (1 - e))
  letI := KerGrp.grp f₁
  have h₁ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst f₁ η[o.A ⊗ o.A]) x ↔ KilledBy ρ w x := by
    intro T x; rw [inSub_ker, hw', killedBy_pair]
  have h₂ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst f₂ η[o.A ⊗ o.A]) x ↔ KilledBy ρ 𝔟 x := by
    intro T x; rw [inSub_ker, h𝔟', killedBy_pair]
  have h₃ : ∀ (T : Over S) (x : T ⟶ o.A), InSub (pullback.fst (ρ.act g) η[o.A]) x ↔ KilledBy ρ (w * 𝔟) x := by
    intro T x; rw [inSub_ker, hmul, killedBy_span]; simp
  have d₃ : IsIsogDeg (toUnit (ker (ρ.act g)))
      (Ideal.absNorm w ^ (D.m * D.n) * Ideal.absNorm 𝔟 ^ (D.m * D.n)) := by
    rw [← mul_pow, ← map_mul, hmul, Ideal.absNorm_span_singleton]
    exact (hI2 g hg0).ker
  have d₂ : IsIsogDeg (toUnit (ker f₂)) (Ideal.absNorm 𝔟 ^ (D.m * D.n)) :=
    GlobalTheory.T.isIsogenyDegree_killedBy_primeToP_harrisTaylor p D R b N S s o hI2 𝔟 hp _ (pullback.fst f₂ η[o.A ⊗ o.A]) inferInstance
      (fun T x => by rw [h₂, killedBy_map])
  have hpos : 0 < Ideal.absNorm 𝔟 ^ (D.m * D.n) :=
    pow_pos (Nat.pos_of_ne_zero (fun h => h𝔟0 (Ideal.absNorm_eq_zero_iff.1 h))) _
  have d₁ := GlobalTheory.T.isIsogenyOfDegree_torsion_coprime_ideals_product S o.A (𝓞 D.F) ρ w 𝔟 hcop _ _ _ (pullback.fst f₁ η[o.A ⊗ o.A])
    (pullback.fst f₂ η[o.A ⊗ o.A]) (pullback.fst (ρ.act g) η[o.A]) inferInstance inferInstance inferInstance
    h₁ h₂ h₃ _ _ hpos d₃ d₂
  refine ⟨ker f₁, KerGrp.grp f₁, pullback.fst f₁ η[o.A ⊗ o.A], KerGrp.isMonHom_fst f₁, inferInstance,
    by rw [← pow_mul]; exact d₁, fun T x => by rw [h₁, killedBy_map]⟩

end GlobalTheory.HTTors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianPelUniformisationOfNorm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UChart

theorem w_zero_mul_conj_eq_norm {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 * H.bar H.w0 = (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
  obtain ⟨m, hm⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have e : (H.d + 1) / 4 = m := by omega
  have hm' : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast hm
  rw [e, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  linear_combination (-(2 * H.w0 + H.rt - 1)) * H.two_weight_eq_one_add_root - H.rt_sq + hm'

theorem exists_sab_pelUnif_of_norm {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type)
    [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    [inst : Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E))
    (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) :
    ∃ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), P.D = D ∧ HEq P.mod inst ∧ HEq P.oD oD := by
  letI := H.starRing
  obtain ⟨G, iG, cG, A, hG, ⟨U⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hR D
  obtain ⟨oA, oG, hl⟩ := _root_.GlobalTheory.Mum.exists_oLinear_of_oAct R hR D A G hG U (𝓞 E) oD
  have hd := H.d_mod
  let t : SAB H (Sp R) :=
    { G := G
      semi := hG
      act := ofRingAct oG
      PP := U.LG
      cub := U.cubG
      sym := GlobalTheory.isSymmetric_of_symmetry_generator U.LG U.symG U.symG_gen U.symG_rig
      adj := fun a => GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star R hR.1 D A G hG U (𝓞 E) oD oA oG hl a
      prim := _root_.GlobalTheory.Mum.mumfordBundle_primitive_of_evenNorm_data R hR D A G hG U (𝓞 E) oD oA oG hl H.w0 ((H.d + 1) / 4)
        (by show H.w0 + H.bar H.w0 = 1; rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]) (w_zero_mul_conj_eq_norm H) (by omega)
        (Nat.even_iff.2 (by omega)) hw }
  exact ⟨t, ⟨D, oD, A, oA, U, rfl, hl, hw⟩, rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.UChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroLiftRealisingKs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (f j)) → ∃ (o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t)) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)), ∀ x ∈ Fil o₀.A, GlobalTheory.FODef.IsFilLiftV m.cart x (LinearMap.pi fun j => f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht φ hφ d f hf
  haveI := GlobalTheory.HTGlue.isArtinianRing_tsze k d
  have hsurj : Function.Surjective (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  have htR : spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t =
      spMap ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp β) := by
    rw [ht]; exact (GlobalTheory.Cris.spMap_comp _ _).symm
  have ht₀ : t = spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫
      (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t) := by
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp]
    have : (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp (algebraMap k (TrivSqZeroExt k (Fin d → k))) = RingHom.id k := by
      ext a; simp
    rw [this]
    simp [spMap]
  have h1 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_hasComplement p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h2 := _root_.GlobalTheory.HTGlue.fil_iff_red_glueFil p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h3 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_order_stable p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h4 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_isotropic_polarisation p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have h5 := GlobalTheory.T.crystalGluedHodgeGraphFiltration_lie_condition p D R b N hN hNp k t o₀ β ht φ hφ d f hf
  have key := GlobalTheory.T.harrisTaylor_exists_squareZero_lift_of_filtration p D R b N hNp (TrivSqZeroExt k (Fin d → k)) k
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom hsurj (GlobalTheory.FODef.sqZero k (Fin d → k))
    ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp β) (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t) t htR ht₀ o₀ (GlobalTheory.HTGlue.glueFil o₀.A f)
  obtain ⟨o, m, hm⟩ := key h1 h2 h3 h4 h5
  refine ⟨o, m, fun x hx => ?_⟩
  obtain ⟨e, he, hce⟩ := GlobalTheory.HTGlue.exists_mem_glueFil o₀.A o₀.ab f hx
  unfold GlobalTheory.FODef.IsFilLiftV
  refine ⟨e, ?_, hce⟩
  rw [hm]; exact he
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedKernelIsogenyTangentInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyUnramified_kernel_isogeny_tangent_injective : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : AbVar K) (f : B ⟶ B), IsIsogeny f → (∀ v : epsPtR (𝟙 (Sp K)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left → v ≫ Hom.hom f = 1 → v = 1) → FormallyUnramified (pullback.snd (Hom.hom f).left η[B.X].left) := by
  first | (exact @GlobalTheory.KerUnram.formallyUnramified_ker) | (exact GlobalTheory.KerUnram.formallyUnramified_ker) | (intros; apply GlobalTheory.KerUnram.formallyUnramified_ker  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericCoordsDescendSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory

theorem gen_level_extends_tate : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ o.eta y = I.ev N y :=
  fun p _ D R _ b N hN hNp S s o k _ _ _ x β hx =>
    GlobalTheory.T.compatible_roots_evaluation_injective p D R b N hN hNp S s o k x β hx (GlobalTheory.T.exists_compatible_roots_and_evaluation p D R b N hN hNp S s o k x β hx)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorAuxiliarySymplecticLevelRepresentablStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_auxiliary_symplectic_level_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SDRep (Module.finrank ℤ D.La / 2) M e → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M := by
  first | (exact @GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable) | (exact GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable) | (intros; apply GlobalTheory.UPel.HT.harrisTaylorModuli_symplecticLevel_representable  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCorrespondenceExtendSourceDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_correspondence_extend_source_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ t₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ s₀ := by
  first | (exact @GlobalTheory.ESValT.extend_source) | (exact GlobalTheory.ESValT.extend_source) | (intros; apply GlobalTheory.ESValT.extend_source <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsIsotropicStableSummandStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_isotropic_stable_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) ∧ (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) := by
  first | exact @GlobalTheory.HTSummand.exists_summand | exact GlobalTheory.HTSummand.exists_summand | (intros; apply GlobalTheory.HTSummand.exists_summand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorKodairaSpencerDirectionsDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem sub_smul_mul_sub_smul_eq_zero_of_quadratic {k E : Type*} [Field k] [Ring E] [Algebra k E] (X : E) (tr nm : ℤ) (r r' : k)
    (hX : X * X = (tr : E) * X - (nm : E)) (hs : r + r' = tr) (hp : r * r' = nm) :
    (X - r • (1 : E)) * (X - r' • (1 : E)) = 0 := by
  have htr : (tr : E) = algebraMap k E r + algebraMap k E r' := by rw [← map_add (f := _), hs, map_intCast]
  have hnm : (nm : E) = algebraMap k E r * algebraMap k E r' := by rw [← map_mul, hp, map_intCast]
  rw [Algebra.smul_def, Algebra.smul_def, _root_.mul_one, _root_.mul_one, sub_mul, mul_sub, mul_sub, hX, htr, hnm,
    ← Algebra.commutes r' X]
  noncomm_ring

end GlobalTheory.HTCount

namespace GlobalTheory.HTCount

theorem ksDim_at_point : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → KSDim (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht φ hφ
  obtain ⟨hfd, hdim, hskew, hiso⟩ := GlobalTheory.T.harrisTaylor_pairing_skew_hodge_lagrangian p D R b N hN hNp k t o₀ β ht φ hφ
  have hnd := _root_.GlobalTheory.HTPolPair.nondeg p D R b N hN hNp k t o₀ β ht φ hφ
  have hadj := GlobalTheory.T.harrisTaylor_crystal_action_adjoint p D R b N hN hNp k t o₀ β ht φ hφ
  have hcount := GlobalTheory.T.harrisTaylor_rho_part_deformation_dim p D R b N hN hNp k t o₀ β ht
  haveI := hfd
  have hstab : ∀ a, ∀ x ∈ Fil o₀.A, crysAct o₀ a x ∈ Fil o₀.A := fun a x hx => by
    haveI := o₀.act.hom a
    rw [crysAct_apply]; exact push_mem_Fil _ hx
  have hcomm : ∀ a, crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) * crysAct o₀ a = crysAct o₀ a * crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) := fun a => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hsurj : Function.Surjective (fun c : D.O => (D.star c).unop) := fun a => ⟨(D.star a).unop, D.star_star a⟩

  have hbar : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
  have hωsq : D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hw2 : algebraMap (𝓞 D.F) D.O D.ω * algebraMap (𝓞 D.F) D.O D.ω =
      (D.tr : D.O) * algebraMap (𝓞 D.F) D.O D.ω - (D.nm : D.O) := by
    rw [← map_mul, hωsq, map_sub, map_mul, map_intCast, map_intCast]
  have hstw : (D.star (algebraMap (𝓞 D.F) D.O D.ω)).unop = (D.tr : D.O) - algebraMap (𝓞 D.F) D.O D.ω := by
    rw [D.star_F, MulOpposite.unop_op, hbar, map_sub, map_intCast]
  have hrr : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k) := by
    have := congrArg β b.ρ_root
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    linear_combination -this
  have hsum : β b.ρ + ((D.tr : k) - β b.ρ) = (D.tr : k) := by ring
  have hdisc : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) ≠ 0 := by
    have hp : p.Prime := Fact.out
    have hnd : ¬ p ∣ (D.tr ^ 2 - 4 * D.nm).natAbs := fun h => D.disc_p (Int.ofNat_dvd_left.2 h)
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    have hu := (b.unit _ hcop).map β
    rw [map_natCast] at hu
    intro h0
    rcases Int.natAbs_eq (D.tr ^ 2 - 4 * D.nm) with e | e
    · rw [e, Int.cast_natCast] at h0; exact hu.ne_zero h0
    · rw [e, Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h0; exact hu.ne_zero h0
  have hne : β b.ρ ≠ (D.tr : k) - β b.ρ := by
    intro h
    apply hdisc
    push_cast
    linear_combination (2 * β b.ρ - (D.tr : k)) * h + 4 * hrr
  have hZ : lieZ o₀ β ≤ LinearMap.range (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨n, lam, c, y, ⟨y₀, rfl⟩, -, rfl⟩
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ⟨crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y₀, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply]
    congr 1
    rw [sub_mul, mul_sub, hcomm, smul_mul_assoc, mul_smul_comm, _root_.one_mul, _root_.mul_one]
  generalize lieZ o₀ β = Z at hZ hcount ⊢
  generalize crysAct o₀ = ρ at hstab hcomm hadj hcount hZ ⊢
  generalize algebraMap (𝓞 D.F) D.O D.ω = w at hw2 hstw hcomm hcount hZ
  have hq := sub_smul_mul_sub_smul_eq_zero_of_quadratic (ρ w) D.tr D.nm (β b.ρ) ((D.tr : k) - β b.ρ)
    (by rw [← map_mul, hw2, map_sub, map_mul, map_intCast, map_intCast]) hsum hrr
  have hwadj : ∀ x y, φ (ρ w x) y = φ x ((β b.ρ + ((D.tr : k) - β b.ρ)) • y - ρ w y) := fun x y => by
    rw [hadj, hstw, map_sub, map_intCast, hsum, LinearMap.sub_apply, Module.End.intCast_apply,
      Int.cast_smul_eq_zsmul]
  exact _root_.GlobalTheory.UPel.Sm.KSCount.ksDim_of_eigen_reduce k (HdR o₀.A) D.O ρ (fun c => (D.star c).unop) φ (Fil o₀.A) Z w (β b.ρ) ((D.tr : k) - β b.ρ) _ hsurj
    hadj hskew hnd hiso hdim hstab hcomm hq hne hwadj hZ hcount

end GlobalTheory.HTCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjIsogeniesRepresentableStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_typeTj_isogenies_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (o₀ : Obj b N (Y.hom ≫ s)) (m₀ : ObjMap o₀ o Y.hom) (o' : Obj b N (Y.hom ≫ s)) (ψ : o₀.A ⟶ o'.A), IsFinite Y.hom ∧ Etale Y.hom ∧ IsPIsog c o₀ o' ψ ∧ IsTj r w j o₀ o' ψ ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (o₁ o₁' : Obj b N (x ≫ s)) (m : ObjMap o₁ o x) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (m₀' : ObjMap o₁ o₀ y) (m₁ : ObjMap o₁' o' y), m₀'.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.IsogRep.exists_rep) | (exact GlobalTheory.UPel.HT.ES.IsogRep.exists_rep) | (intros; apply GlobalTheory.UPel.HT.ES.IsogRep.exists_rep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatSymbolMemMaximalIdealOfKodairaSpencerZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heat_symbol_mem_maximalIdeal_of_kodairaSpencer_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d) := by
  first | exact @GlobalTheory.KSZeroMod.symbol_mem_maximalIdeal | exact GlobalTheory.KSZeroMod.symbol_mem_maximalIdeal | (intros; apply GlobalTheory.KSZeroMod.symbol_mem_maximalIdeal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeGroupCohomologyStrictlyHenselian
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem GlobalTheory.gm_cohomology_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  first
  | exact @_root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology
  | exact _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology
  | (apply _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> assumption)
  | (intros; apply _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology ..)
end

