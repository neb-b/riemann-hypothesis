module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0013
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CardCount
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem card_count (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E) (hG1 : ∀ a a', G₀ a a' ∈ M.L.O) :
    Nat.card (Set.range fun v : {v : ι → V // H.Prim Λ v ∧ ∀ a a', H.h (v a') (v a) - G₀ a a' ∈
        Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
      fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (v.1 a)) =
    Nat.card {X : ι → Fin n → k // LinearIndependent k X ∧
      ∀ a a', ∑ i, ∑ j, X a' i * Ph r H b hint i j * X a j ^ q = r ⟨G₀ a a', hG1 a a'⟩} := by
  let Φ : {v : ι → V // H.Prim Λ v ∧ ∀ a a', H.h (v a') (v a) - G₀ a a' ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} →
      {X : ι → Fin n → k // LinearIndependent k X ∧
        ∀ a a', ∑ i, ∑ j, X a' i * Ph r H b hint i j * X a j ^ q = r ⟨G₀ a a', hG1 a a'⟩} :=
    fun v => ⟨fun a => red hR (v.1 a), (prim_iff hR H hϖ o2 o3 v.1 v.2.1.1).1 v.2.1,
      fun a a' => (gram_cond_iff hR H hint q rfrob (v.2.1.1 a') (v.2.1.1 a) (G₀ a a') (hG1 a a')).1 (v.2.2 a a')⟩
  have hsurj : Function.Surjective Φ := by
    intro X
    choose x hxΛ hxr using fun a => red_lift hR (X.1 a)
    have hfx : (fun a => red hR (x a)) = X.1 := funext hxr
    have hli : LinearIndependent k (fun a => red hR (x a)) := by rw [hfx]; exact X.2.1
    refine ⟨⟨x, (prim_iff hR H hϖ o2 o3 x hxΛ).2 hli, fun a a' =>
      (gram_cond_iff hR H hint q rfrob (hxΛ a') (hxΛ a) (G₀ a a') (hG1 a a')).2 ?_⟩, ?_⟩
    · rw [hxr, hxr]; exact X.2.2 a a'
    · exact Subtype.ext hfx
  refine Nat.card_congr ((Setoid.quotientKerEquivRange _).symm.trans
    ((Quotient.congrRight ?_).trans (Setoid.quotientKerEquivOfSurjective Φ hsurj)))
  intro v v'
  rw [Setoid.ker_def, Setoid.ker_def]
  constructor
  · intro h
    apply Subtype.ext
    funext a
    have h1 := congrFun h a
    rw [Submodule.Quotient.eq] at h1
    exact (class_iff hR H (v.2.1.1 a) (v'.2.1.1 a)).1 h1
  · intro h
    funext a
    have h1 := congrFun (congrArg Subtype.val h) a
    rw [Submodule.Quotient.eq]
    exact (class_iff hR H (v.2.1.1 a) (v'.2.1.1 a)).2 h1

end FC

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFR
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

theorem fr_max {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    (Ideal.span {piO L ϖ}).IsMaximal := by
  have hinj := fl_inj L
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h1
    rw [Ideal.mem_span_singleton'] at h1
    obtain ⟨z, hz⟩ := h1
    have hz' : (z : E) * algebraMap F E ϖ = 1 := by
      have := congrArg Subtype.val hz
      simpa [piO] using this
    have hϖ0 : (ϖ : F) ≠ 0 := by
      intro h; apply hϖ.ne_zero; exact Subtype.ext h
    have hzF : (z : E) = algebraMap F E (ϖ : F)⁻¹ := by
      have h2 : algebraMap F E (ϖ : F) * algebraMap F E (ϖ : F)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one]
      calc (z : E) = (z : E) * (algebraMap F E ϖ * algebraMap F E (ϖ : F)⁻¹) := by rw [h2, mul_one]
        _ = algebraMap F E (ϖ : F)⁻¹ := by rw [← mul_assoc, hz', one_mul]
    have hmem : (ϖ : F)⁻¹ ∈ 𝒪[F] := fl_mem_int L hinj (hzF ▸ z.2)
    apply hϖ.not_isUnit
    have h3 : ϖ * ⟨_, hmem⟩ = 1 := Subtype.ext (by
      show (ϖ : F) * (ϖ : F)⁻¹ = 1
      exact mul_inv_cancel₀ hϖ0)
    exact ⟨⟨ϖ, ⟨_, hmem⟩, h3, by rw [mul_comm]; exact h3⟩, rfl⟩
  · intro J x hIJ hx hxJ
    have hnd : ¬ ∃ z ∈ L.O, (x : E) = algebraMap F E ϖ * z := by
      rintro ⟨z, hz, hxz⟩
      apply hx
      rw [Ideal.mem_span_singleton']
      exact ⟨⟨z, hz⟩, Subtype.ext (by simp [piO, hxz, mul_comm])⟩
    obtain ⟨y, hy, hxy⟩ := fl_local L hl hE hinj ϖ hϖ x x.2 hnd
    have : (1 : L.O) = x * ⟨y, hy⟩ := Subtype.ext (by simp [hxy])
    rw [this]
    exact J.mul_mem_right _ hxJ

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Stage1OfUnipotentIntegralIsGroup
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem stage1_riesz (D : Formalism.BasicNotions.D7) (φ : (VS D).V →ₗ[D.host.E] D.host.E) : ∃ μ : (VS D).V, ∀ v, (VS D).hT μ v = φ v := by
  classical
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis (VS D).hT (VS D).nondeg (VS D).frame
  refine ⟨∑ j, star (φ ((VS D).frame j)) • bs j, fun v => ?_⟩
  have key : (VS D).hT (∑ j, star (φ ((VS D).frame j)) • bs j) = φ := by
    apply (VS D).frame.ext
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    have hs : ∀ j, (VS D).hT (star (φ ((VS D).frame j)) • bs j) ((VS D).frame i) =
        φ ((VS D).frame j) * (if i = j then 1 else 0) := by
      intro j
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      congr 1
      rw [← (VS D).herm.eq ((VS D).frame i) (bs j), hbs]
      split_ifs <;> simp
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [key]

private theorem stage1_span_eq_top_of_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨μ, hμ⟩ := stage1_riesz D φ
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using (hμ y).symm
  have hline (a : D.host.E) : a • μ ∈ Λ := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual (VS D).hT Λ
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← (VS D).herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule D.host.E (VS D).V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 D.host.E)
  have hmap (x : D.host.E) : x ∈ Λ.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 D.host.E)) (hL.map f)
  have hinj := IsFractionRing.injective (𝓞 D.host.E) D.host.E
  have hne {a : 𝓞 D.host.E} (ha : a ≠ 0) : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : D.host.E) : IsLocalization.IsInteger (𝓞 D.host.E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField D.host.E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 D.host.E) D.host.E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]


theorem inW_neg (D : Formalism.BasicNotions.D7) {x : (VS D).V} (hx : InW D x) : InW D (-x) := by
  simpa using inW_smul D (-1) hx

theorem stage1_of_unipotentIntegralIsGroup (hN : UnipotentIntegralIsGroup) : Stage1 := by
  intro D T T' F0 Λ hF Z R hR
  have hF' := hF
  obtain ⟨hlat, hU, he, heΛ0, c0, hc0, hz⟩ := hF
  have heΛ : ∀ a, D.sp.hypE a ∈ Λ := fun a => by rw [← he]; exact heΛ0 a
  let : Submodule.IsLattice D.host.E Λ := hlat
  have hfull : Submodule.IsFullLattice D.host.E Λ :=
    ⟨stage1_span_eq_top_of_unimodular D hlat.fg hU⟩
  obtain ⟨d, hd0, hdv, hdk⟩ := common_mult D hfull
    (Finset.univ.image D.sp.hypF ∪ {((D.sp.T : D.host.E)⁻¹) • D.sp.zm})
    (Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2) ∪
      Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Pm D Z R p.1 p.2))
  have hdF : ∀ a, (d : D.host.E) • D.sp.hypF a ∈ Λ := fun a =>
    hdv _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))
  have hdz : ((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm ∈ Λ := by
    rw [← smul_smul]; exact hdv _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hdR : ∀ b a, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (d : D.host.E) * R b a := fun b a =>
    hdk _ (Finset.mem_union_left _ (Finset.mem_image_of_mem (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2)
      (Finset.mem_univ (b, a))))
  have hdP : ∀ b' b, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (d : D.host.E) * Pm D Z R b' b :=
    fun b' b => hdk _ (Finset.mem_union_right _ (Finset.mem_image_of_mem
      (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Pm D Z R p.1 p.2) (Finset.mem_univ (b', b))))
  have hd2 : ∀ v ∈ Λ, (d : D.host.E) ^ 2 • pW D v ∈ Λ := fun v hv => pW_lat D hU heΛ d hdF hdz hv
  have hdE : (d : D.host.E) ≠ 0 := Int.cast_ne_zero.2 hd0
  have hd3 : (d : D.host.E) ^ 3 ≠ 0 := pow_ne_zero 3 hdE
  have hΛfg : (Λ.restrictScalars ℤ).FG := Submodule.FG.restrictScalars hlat.fg

  let Sb : Fin (D.R.rS + 1) → Set (VS D).V := fun b =>
    {w | w ∈ Λ.restrictScalars ℤ ∧ (∀ a, (VS D).hT (D.sp.hypE a) w = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) w = 0) ∧
      (VS D).hT D.sp.zm w = 0 ∧ (VS D).hT w w = (d : D.host.E) ^ 6 * kap D T' Z R c0 b}
  have hSb : ∀ b, (Sb b).Finite := fun b => definite_finite D _ hΛfg _
  let Tset : Fin (D.R.rS + 1) → Set (VS D).V := fun b => (fun w => (((d : D.host.E) ^ 3)⁻¹) • w) '' Sb b

  have hLWfg : ((LamW D Λ).restrictScalars ℤ).FG := Submodule.FG.of_le hΛfg (fun y hy => hy.1)
  obtain ⟨Rs, hRs, hred⟩ := gen_red _ hLWfg (2 * d ^ 3) (mul_ne_zero two_ne_zero (pow_ne_zero 3 hd0))
  refine ⟨(fun p : (Fin (D.R.rS + 1) → (VS D).V) × (Fin D.R.rS → (VS D).V) =>
      fun b => p.1 b + (((d : D.host.E) ^ 3)⁻¹) • ∑ a, betaZ D Z a b • p.2 a) ''
      (Set.pi Set.univ Tset ×ˢ Set.pi Set.univ (fun _ => Rs)), ?_, ?_⟩
  · exact ((Set.Finite.pi (fun b => (hSb b).image _)).prod (Set.Finite.pi (fun _ => hRs))).image _
  intro x hx
  have hbeta : ∀ (a : Fin D.R.rS) b, (VS D).hT (D.sp.hypE a) (fr D x b) = betaZ D Z a b := by
    intro a b
    have := hx.2.1 (Fin.castSucc a) b
    simpa [brS, FlagG.fvec, he, betaZ] using this

  have hw2 : ∀ b, (d : D.host.E) ^ 2 • pWf D x b ∈ LamW D Λ := fun b =>
    ⟨hd2 _ (hx.1 b), inW_smul D _ (inW_pW D _)⟩
  have hu : ∀ a, (d : D.host.E) ^ 3 • (∑ b, R b a • pWf D x b) ∈ (LamW D Λ).restrictScalars ℤ := by
    intro a
    have : (d : D.host.E) ^ 3 • (∑ b, R b a • pWf D x b) =
        ∑ b, ((d : D.host.E) * R b a) • ((d : D.host.E) ^ 2 • pWf D x b) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [smul_smul, smul_smul]; ring_nf
    rw [Submodule.restrictScalars_mem, this]
    refine Submodule.sum_mem _ fun b _ => ?_
    obtain ⟨o, ho⟩ := hdR b a
    rw [← ho, algebraMap_smul]
    exact (LamW D Λ).smul_mem o (hw2 b)
  choose q hq ρ hρ hqρ using fun a => hred _ (hu a)
  obtain ⟨n, hn, hpW⟩ := eich_all hN D F0 Λ hF' (fun a => -q a) (fun a => inW_neg D (hq a).2)
    (fun a => Λ.neg_mem (hq a).1)
  refine ⟨n, hn, ⟨(tv D Z R x, ρ), ⟨fun b _ => ?_, fun a _ => hρ a⟩, ?_⟩⟩
  ·
    refine ⟨(d : D.host.E) ^ 3 • tv D Z R x b, ⟨?_, ?_, ?_, ?_, ?_⟩, inv_smul_smul₀ hd3 _⟩
    · rw [Submodule.restrictScalars_mem]
      have : (d : D.host.E) ^ 3 • tv D Z R x b =
          ∑ b', ((d : D.host.E) * Pm D Z R b' b) • ((d : D.host.E) ^ 2 • pWf D x b') := by
        rw [tv, Finset.smul_sum]
        exact Finset.sum_congr rfl fun b' _ => by rw [smul_smul, smul_smul]; ring_nf
      rw [this]
      refine Submodule.sum_mem _ fun b' _ => smul_int_mem D (hdP b' b) (hw2 b').1
    all_goals have hW : InW D ((d : D.host.E) ^ 3 • tv D Z R x b) :=
      inW_smul D _ (inW_sum D _ _ fun b' => inW_smul D _ (inW_pW D _))
    · exact hW.1
    · exact hW.2.1
    · exact hW.2.2
    · simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply,
        star_pow, star_intCast]
      rw [tv_norm D T' F0 Λ Z R hR he hc0 hz hx b]
      ring
  ·
    funext b
    have h2q : ∀ a, (2 : D.host.E) • q a = (∑ b', R b' a • pWf D x b') - (((d : D.host.E) ^ 3)⁻¹) • ρ a := by
      intro a
      have e1 := hqρ a
      rw [← Int.cast_smul_eq_zsmul D.host.E] at e1
      have e2 : ((2 * d ^ 3 : ℤ) : D.host.E) • q a = (d : D.host.E) ^ 3 • (∑ b', R b' a • pWf D x b') - ρ a := by
        rw [e1]; abel
      have e3 : (2 : D.host.E) • q a = (((d : D.host.E) ^ 3)⁻¹) • (((2 * d ^ 3 : ℤ) : D.host.E) • q a) := by
        rw [smul_smul]; congr 1; push_cast; field_simp
      rw [e3, e2, smul_sub, inv_smul_smul₀ hd3]
    symm
    show pW D (fr D (act D n x) b) = tv D Z R x b + (((d : D.host.E) ^ 3)⁻¹) • ∑ a, betaZ D Z a b • ρ a
    rw [fr_act, hpW]
    have e4 : ∀ a, (VS D).hT (D.sp.hypE a) (fr D x b) • ((2 : D.host.E) • -q a) =
        -(betaZ D Z a b • (∑ b', R b' a • pWf D x b')) + (((d : D.host.E) ^ 3)⁻¹) • (betaZ D Z a b • ρ a) := by
      intro a
      rw [hbeta, smul_neg, h2q, smul_neg, smul_sub, smul_comm (betaZ D Z a b) (((d : D.host.E) ^ 3)⁻¹) (ρ a)]
      abel
    rw [Finset.sum_congr rfl fun a _ => e4 a, Finset.sum_add_distrib, ← Finset.smul_sum]
    simp only [tv, Pm, Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mul_apply, Finset.sum_smul,
      Finset.sum_neg_distrib, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm (f := fun a b' => (betaZ D Z a b * R b' a) • pWf D x b')]
    have e5 : ∀ b' a, (betaZ D Z a b * R b' a) • pWf D x b' = (R b' a * betaZ D Z a b) • pWf D x b' :=
      fun b' a => by rw [mul_comm]
    simp only [e5]
    show pW D (fr D x b) + _ = _
    have e6 : pWf D x b = pW D (fr D x b) := rfl
    rw [← e6]
    abel

end PI.UnitaryGroupMassFormula.CntFormula
end
end

