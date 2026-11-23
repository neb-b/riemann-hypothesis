module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import ReciprocityTheory.SemistableReduction.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPair
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.ShareOn.WhitBase

section SlopeTestRemainingChoices

open Formalism.L2.DIV

variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}

theorem isUniUp_map_iff (f : κ ≃+* κ') (M : GL (Fin r) κ) :
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp ((Matrix.GeneralLinearGroup.map f.toRingHom M : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') ↔
      M ∈ unip κ r := by
  have hc : ∀ a b, ((Matrix.GeneralLinearGroup.map f.toRingHom M : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') a b =
      f ((M : Matrix (Fin r) (Fin r) κ) a b) := fun a b => rfl
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := (h i j).1 hij
      rw [hc] at this
      exact f.injective (by rw [this, map_zero])
    · have := (h i i).2 rfl
      rw [hc] at this
      exact f.injective (by rw [this, map_one])
  · intro h a b
    refine ⟨fun hab => ?_, fun hab => ?_⟩
    · rw [hc, unip_lower h hab, map_zero]
    · subst hab
      rw [hc, unip_diag h, map_one]

theorem edgeSum_supEdge_eq (M : GL (Fin r) κ) :
    edgeSum supEdge M = ∑ i ∈ Finset.range (r - 1), Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) i (i + 1) := by
  classical
  have h1 : ∀ i : Fin r, (∑ j : Fin r, if supEdge i j then (M : Matrix (Fin r) (Fin r) κ) i j else 0) =
      Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) i.val (i.val + 1) := by
    intro i
    unfold Formalism.MainNotions.ArithmeticCylinders.entN
    by_cases hi : i.val + 1 < r
    · rw [Finset.sum_eq_single ⟨i.val + 1, hi⟩]
      · rw [if_pos (show supEdge i ⟨i.val + 1, hi⟩ from rfl), dite_eq_left ⟨i.isLt, hi⟩]
      · intro j _ hj
        rw [if_neg (show ¬ supEdge i j from fun e => hj (Fin.ext e))]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dite_eq_right (by omega)]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg (show ¬ supEdge i j from fun e => by
        have := j.isLt
        unfold supEdge at e
        omega)]
  unfold edgeSum
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) i (i + 1)) r]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Finset.sum_range_succ, Nat.add_sub_cancel]
    have : Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) s (s + 1) = 0 := by
      unfold Formalism.MainNotions.ArithmeticCylinders.entN
      rw [dite_eq_right (by omega)]
    rw [this, add_zero]

theorem entN_map (f : κ ≃+* κ') (M : GL (Fin r) κ) (a b : ℕ) :
    Formalism.MainNotions.ArithmeticCylinders.entN ((Matrix.GeneralLinearGroup.map f.toRingHom M : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') a b =
      f (Formalism.MainNotions.ArithmeticCylinders.entN (M : Matrix (Fin r) (Fin r) κ) a b) := by
  unfold Formalism.MainNotions.ArithmeticCylinders.entN
  split_ifs
  · rfl
  · rw [map_zero]

end SlopeTestRemainingChoices

section Comparison₂

open Formalism.L2.DIV Formalism.BasicNotions

variable {D : D7} {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G}
  {ψs : Ps →* D.what₂.LLˣ} {eG : G ≃* G0g D.nd} {Pg : Finset (Pl D.host.E)}
  {pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg} {res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)}
  {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC : G ≃* G0 Pg D.R.r}

theorem mem_iff_of_lvlTie (h : LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC) (g : G) :
    g ∈ P0 ↔ ∀ kv, Formalism.MainNotions.ArithmeticCylinders.IsUniUp ((eG g kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  rw [h.p0 g]
  show eC g ∈ Subgroup.pi Set.univ _ ↔ _
  rw [Subgroup.mem_pi]
  constructor
  · intro hx kv
    rw [h.comp g kv, isUniUp_map_iff]
    exact hx (pl kv) (Set.mem_univ _)
  · intro hx PP _
    obtain ⟨kv, rfl⟩ := pl.surjective PP
    have := hx kv
    rw [h.comp g kv, isUniUp_map_iff] at this
    exact this

theorem chi_of_lvlTie (h : LvlTie D P0 ψ0 Ps ψs eG Pg pl res ψ eC) (g : P0)
    (hg : eC g ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ).H) :
    ((ψ0 g : D.what₂.LLˣ) : D.what₂.LL) = ∏ PP : ↥Pg, ψ PP.1 (edgeSum supEdge (eC g PP)) := by
  rw [h.chi0 g hg]
  unfold Formalism.L2.DIV.P0 LevelP.ofLocal
  dsimp only
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  exact Finset.prod_congr rfl fun PP _ => rfl

end Comparison₂

end GlobalTheory.ShareOn.WhitBase

namespace GlobalTheory.ShareOn

open GlobalTheory.ShareOn.WhitBase


end GlobalTheory.ShareOn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentDatumLeOfPrimePowerLatticeInclusion
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.ExpTie

theorem exists_mul_eq_prW_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (J : ℕ) {a : 𝓞 K}
    (ha : a ∈ w.asIdeal ^ (J * Formalism.L2.Col.eW w)) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ b : 𝓞 K, t * a = ((Formalism.L2.Col.prW w : ℕ) : 𝓞 K) ^ J * b := by
  have hm := (Formalism.L2.Col.algebraMap_mem_maximalIdeal_pow_iff w a (J * Formalism.L2.Col.eW w)).2 ha
  rw [mul_comm, pow_mul, ← Formalism.L2.Col.span_prW_ow, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
  obtain ⟨y, hy⟩ := hm
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl y
  refine ⟨t, t.2, b, ?_⟩
  apply IsLocalization.injective (Formalism.L2.Col.Ow w) w.asIdeal.primeCompl_le_nonZeroDivisors
  rw [map_mul, map_mul, hy, map_pow, map_natCast, mul_comm, mul_assoc, IsLocalization.mk'_spec]

theorem LIncl.jexpU_bounds {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : Formalism.L2.DIV.BlockDat K G Pl0} {ℓ : Formalism.L2.DIV.Lvl K G} {Z : Submodule K B.S.Forms} {w : HeightOneSpectrum (𝓞 K)} {J : ℕ}
    (h : LIncl B ℓ Z w J) : 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J := by
  have he : 0 < Formalism.L2.Col.eW w := Formalism.L2.Col.eW_pos w
  have hp : Formalism.EigenvalueLevelCeiling.plc w = Formalism.L2.Col.prW w :=
    Formalism.L2.Col.eq_prW_of_mem w (Formalism.EigenvalueLevelCeiling.plc_prime w) (Formalism.EigenvalueLevelCeiling.plc_mem w)
  have key : B.JexpW ℓ Z w ≤ J * Formalism.L2.Col.eW w := by
    unfold Formalism.L2.DIV.BlockDat.JexpW Formalism.L2.DIV.expW
    apply Nat.sInf_le
    intro a ha z hz
    obtain ⟨t, ht, b, htb⟩ := exists_mul_eq_prW_pow w J ha
    obtain ⟨s, hs, hsz⟩ := h z hz
    refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
    have e : (s * t) • (a • z) = b • (s • ((((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ J) • z)) := by
      rw [hp, smul_smul, smul_smul, smul_smul, mul_assoc, htb]
      congr 1
      ring
    rw [e]
    exact Submodule.smul_mem _ b hsz
  refine ⟨?_, ?_⟩
  · unfold Formalism.L2.DIV.BlockDat.JexpU
    positivity
  · unfold Formalism.L2.DIV.BlockDat.JexpU
    rw [div_le_iff₀ (by exact_mod_cast he)]
    exact_mod_cast key

theorem jexpU_le_of_lIncl : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type)
    (B : Formalism.L2.DIV.BlockDat K G Pl0) (ℓ : Formalism.L2.DIV.Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ),
    LIncl B ℓ Z w J → 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => LIncl.jexpU_bounds h

end GlobalTheory.ExpTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicDualBasisIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_dual_basis_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F)), (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) → (∀ i j, g i (yy j) = if i = j then 1 else 0) →
    ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ y : (κ → FiniteAdeleRing (𝓞 F) F), ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2 ≤
        C * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
  first | exact @GlobalTheory.WeilL2Words.slice_le_l2A | exact GlobalTheory.WeilL2Words.slice_le_l2A | (intros; apply GlobalTheory.WeilL2Words.slice_le_l2A <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsDefiniteUnitaryFlagDom
section
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.DefiniteFin

theorem finiteDimensional_span_of_slices (ι : Type) [Fintype ι] [DecidableEq ι] (A : ι → Type) (D : ∀ i, Set (A i))
    (W : ∀ i, Submodule ℂ (A i → ℂ)) (hW : ∀ i, FiniteDimensional ℂ (W i)) (Dom : Set (∀ i, A i))
    (hDom : Dom = Set.univ.pi D) (S : Set ((∀ i, A i) → ℂ))
    (hS : ∀ g ∈ S, ∀ x ∈ Dom, ∀ i, ∃ w ∈ W i, ∀ t ∈ D i, g (Function.update x i t) = w t) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun g : (∀ i, A i) → ℂ => fun x : Dom => g x) '' S)) := by
  subst hDom
  have hT : ∀ i, ∃ T : Set (A i), T ⊆ D i ∧ T.Finite ∧
      ∀ w ∈ W i, (∀ t ∈ T, w t = 0) → ∀ t ∈ D i, w t = 0 := by
    intro i
    let ev : A i → Module.Dual ℂ (W i) := fun t =>
      (LinearMap.proj t : (A i → ℂ) →ₗ[ℂ] ℂ).comp (W i).subtype
    obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℂ (ev '' D i)
    have hbfin : b.Finite := hli.setFinite
    obtain ⟨T, hTD, hTfin, hTb⟩ := Set.exists_subset_image_finite_and.1 ⟨b, hb, hbfin, rfl⟩
    refine ⟨T, hTD, hTfin, fun w hw h0 t ht => ?_⟩
    have hmem : ev t ∈ Submodule.span ℂ b := by
      rw [hspan]; exact Submodule.subset_span ⟨t, ht, rfl⟩
    have hall : ∀ φ ∈ Submodule.span ℂ b, φ ⟨w, hw⟩ = 0 := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem φ hφ =>
        rw [hTb] at hφ
        obtain ⟨s, hs, rfl⟩ := hφ
        exact h0 s hs
      | zero => rfl
      | add φ ψ _ _ h1 h2 => simp [h1, h2]
      | smul c φ _ h => simp [h]
    exact hall _ hmem
  choose T hTD hTfin hTz using hT
  let G : Set (∀ i, A i) := Set.univ.pi T
  have hGfin : G.Finite := Set.Finite.pi (fun i => hTfin i)
  have hGD : G ⊆ Set.univ.pi D := Set.pi_mono (fun i _ => hTD i)
  let V : Submodule ℂ ((∀ i, A i) → ℂ) :=
    { carrier := {g | ∀ x ∈ Set.univ.pi D, ∀ i, ∃ w ∈ W i, ∀ t ∈ D i, g (Function.update x i t) = w t}
      add_mem' := by
        intro f g hf hg x hx i
        obtain ⟨w, hw, hfw⟩ := hf x hx i
        obtain ⟨w', hw', hgw⟩ := hg x hx i
        exact ⟨w + w', (W i).add_mem hw hw', fun t ht => by simp [hfw t ht, hgw t ht]⟩
      zero_mem' := by
        intro x hx i
        exact ⟨0, (W i).zero_mem, fun t ht => by simp⟩
      smul_mem' := by
        intro c f hf x hx i
        obtain ⟨w, hw, hfw⟩ := hf x hx i
        exact ⟨c • w, (W i).smul_mem c hw, fun t ht => by simp [hfw t ht]⟩ }
  have key : ∀ g ∈ V, (∀ x ∈ G, g x = 0) → ∀ x ∈ Set.univ.pi D, g x = 0 := by
    intro g hg h0
    have hs : ∀ s : Finset ι, ∀ x ∈ Set.univ.pi D, (∀ i ∉ s, x i ∈ T i) → g x = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro x _ hx; exact h0 x (fun i _ => hx i (Finset.notMem_empty i))
      | insert j s hj ih =>
        intro x hx hxT
        obtain ⟨w, hw, hgw⟩ := hg x hx j
        have hwT : ∀ t ∈ T j, w t = 0 := by
          intro t ht
          rw [← hgw t (hTD j ht)]
          apply ih
          · intro i _
            by_cases h : i = j
            · subst h; simpa using hTD i ht
            · simpa [h] using hx i trivial
          · intro i hi
            by_cases h : i = j
            · subst h; simpa using ht
            · simpa [h] using hxT i (by simp [h, hi])
        have h1 := hTz j w hw hwT (x j) (hx j trivial)
        rw [← h1, ← hgw (x j) (hx j trivial), Function.update_eq_self]
    intro x hx
    exact hs Finset.univ x hx (fun i hi => absurd (Finset.mem_univ i) hi)
  let resD : ((∀ i, A i) → ℂ) →ₗ[ℂ] (Set.univ.pi D → ℂ) := LinearMap.funLeft ℂ ℂ Subtype.val
  let resG : (Set.univ.pi D → ℂ) →ₗ[ℂ] (G → ℂ) := LinearMap.funLeft ℂ ℂ (Set.inclusion hGD)
  have hsub : Submodule.span ℂ ((fun g : (∀ i, A i) → ℂ => fun x : Set.univ.pi D => g x) '' S) ≤
      V.map resD := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hS g hg, rfl⟩
  haveI : Finite G := hGfin.to_subtype
  have hinj : Function.Injective (resG.domRestrict (V.map resD)) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨φ, g, hg, rfl⟩ hφ
    rw [LinearMap.mem_ker] at hφ
    rw [Submodule.mem_bot]
    ext ⟨x, hx⟩
    have hz : ∀ y ∈ G, g y = 0 := by
      intro y hy
      have := congrFun (show resG (resD g) = 0 from hφ) ⟨y, hy⟩
      exact this
    exact key g hg hz x hx
  haveI : FiniteDimensional ℂ (V.map resD) := Module.Finite.of_injective _ hinj
  exact Submodule.finiteDimensional_of_le hsub

theorem finiteDimensional_cusp_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ la : Wt X.Ψ r,
      FiniteDimensional ℂ (Submodule.span ℂ ((fun f : Frame X.Ψ r → ℂ => fun x : X.dom => f x) '' X.SS la)) := by
  intro E _ _ _ r X hp la
  classical
  have hdom : ∀ x : Frame X.Ψ r, x ∈ X.dom ↔ ∀ τ, (mat x τ).det ≠ 0 := by
    intro x
    constructor
    · intro hx τ; exact (hx τ).1
    · intro hx τ; exact ⟨hx τ, _root_.GlobalTheory.FlagDomain.definite_frame_leading_minors_sign E r X hp x τ (hx τ)⟩
  set N : ℕ := ∑ τ, ∑ i, (la τ i).natAbs with hN
  have hNle : ∀ τ i, 0 ≤ la τ i + N := by
    intro τ i
    have h1 : (la τ i).natAbs ≤ N := by
      calc (la τ i).natAbs ≤ ∑ i, (la τ i).natAbs :=
            Finset.single_le_sum (f := fun i => (la τ i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ ≤ N := Finset.single_le_sum (f := fun τ => ∑ i, (la τ i).natAbs) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ τ)
    omega
  let d : X.Ψ → ℕ := fun τ => ∑ i, (la τ i + N).toNat
  let ev : MvPolynomial (Fin r × Fin r) ℂ →ₗ[ℂ] ((Fin r → Fin r → ℂ) → ℂ) :=
    { toFun := fun F y => MvPolynomial.eval (fun ij => y ij.1 ij.2) F * ((Matrix.of y).det)⁻¹ ^ N
      map_add' := by intro F G; funext y; simp [add_mul]
      map_smul' := by intro c F; funext y; simp [mul_assoc] }
  let W : X.Ψ → Submodule ℂ ((Fin r → Fin r → ℂ) → ℂ) :=
    fun τ => (MvPolynomial.restrictTotalDegree (Fin r × Fin r) ℂ (d τ)).map ev
  have hW : ∀ τ, FiniteDimensional ℂ (W τ) := fun τ => inferInstance
  refine finiteDimensional_span_of_slices X.Ψ (fun _ => Fin r → Fin r → ℂ) (fun _ => {y | (Matrix.of y).det ≠ 0})
    W hW X.dom ?_ (X.SS la) ?_
  · ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
    exact hdom x
  · intro g hg x hx τ
    obtain ⟨F, hF, hFy⟩ := _root_.GlobalTheory.section_slice_eq_poly_div_det_pow E r X hdom la N hNle g hg.1.1 x hx τ
    refine ⟨ev F, ⟨F, ?_, rfl⟩, fun t ht => hFy t ht⟩
    rw [SetLike.mem_coe, MvPolynomial.mem_restrictTotalDegree]
    exact hF.totalDegree_le

end GlobalTheory.DefiniteFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartQuadraticPhaseEqCmThetaExpStatement
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePartQuadraticPhase_eq_cmTheta_exp : ∀ D : D7, ∃ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 ∧
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E),
  Setup ψ θ S T cc δ r → ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
  ψ (-symplOH S T (GlobalTheory.FinWeilO.intA D w • finPt (S := S) (T := T) rfl rfl r z) (finPt (S := S) (T := T) rfl rfl r z)) =
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  first | exact @GlobalTheory.SplitPhase.phase_eq | exact GlobalTheory.SplitPhase.phase_eq | (intros; apply GlobalTheory.SplitPhase.phase_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfCosetIndicatorModIdealIsSchwartzBruhatHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfCosetIndicatorModIdeal_isSchwartzBruhatHalf : ∀ {D : D7} (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    Submodule.IsFullLattice D.host.E LS → Submodule.IsFullLattice D.host.E LT → ∀ (a : Formalism.L2.Theta.AE D), infPart D a = 0 →
    ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ x : WO S T, IsHalf a x → IsSBHalf a (latO S T LS LT fun _ => True) (cosetFn a I x) := by
  first
  | exact @GlobalTheory.BotSmallDict.cosetFn_isSBHalf
  | intro D S T LS LT hS hT a ha I hI x hx
    exact GlobalTheory.BotSmallDict.cosetFn_isSBHalf S T LS LT hS.toIsLattice hT.toIsLattice a ha I hI x hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergStableRelationOfVacuaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergStableRelation_of_vacua : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ →
    ∀ {ι : Type} (P : Finset ι) (pl : ι → HeightOneSpectrum (𝓞 F)), Set.InjOn pl P →
    ∀ (Z : ι → Type) [∀ w, TopologicalSpace (Z w)] [∀ w, Add (Z w)]
      (A A' : ι → Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
      (co : ∀ w, Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z w)
      (I : ∀ w, ((Fin n × Fin d → Fv F (pl w)) → ℂ) →ₗ[ℂ] (Z w → ℂ))
      (H : AddSubgroup (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
      (R : Submodule ℂ ((Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ) × ((Fin n × Fin d → AF F) → ℂ)))
      (f : SInf F (Fin n × Fin d)),
    (∀ w ∈ P, IsLagrModel M ψ (pl w) (A w) (A' w) (co w) (I w)) →
    (∀ w ∈ P, ∀ u ∈ A w, At (evFin F (pl w)) u ∧ u ∈ H) → (∀ w ∈ P, ∀ u ∈ A' w, At (evFin F (pl w)) u) →
    (∀ w ∈ P, ∀ u, At (evFin F (pl w)) u → ∃ x ∈ A w, ∃ y ∈ A' w, u = x + y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ u, co w (u + x) = co w u + co w x) →
    (∀ w ∈ P, ∀ w' ∈ P, w' ≠ w → ∀ x ∈ A w, ∀ u, co w' (u + x) = co w' u) →
    (∀ w ∈ P, ∀ u, ∃ x ∈ A w, co w x = co w u ∧ ∀ y ∈ A' w,
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y =
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ p ∈ R, (fun u => p.1 (u + x), M.co.rho ψ x p.2) ∈ R) →
    (∀ w ∈ P, ∀ y ∈ A' w, ∀ p ∈ R, (fun u => ψ (symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y) * p.1 u, M.co.rho ψ y p.2) ∈ R) →
    (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (M.vac (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) ∈ R →
    ∀ φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ v, (∀ w ∈ P, pl w ≠ v) → φ v = M.vac v) →
      (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (φ (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ R := by
  first | exact @GlobalTheory.InductLagr.rel_of_vac | exact GlobalTheory.InductLagr.rel_of_vac | (intros; apply GlobalTheory.InductLagr.rel_of_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhatStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_eq_zero_of_kills_productSchwartzBruhat : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ Λ : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), Λ (boxFun φ₁ φ₂) = 0) → ∀ Φ ∈ SB (κ ⊕ κ' → Fv F v), Λ Φ = 0 := by
  first | exact @GlobalTheory.BoxSpan.boxSpan_ker | exact GlobalTheory.BoxSpan.boxSpan_ker | (intros; apply GlobalTheory.BoxSpan.boxSpan_ker <;> assumption)
end

